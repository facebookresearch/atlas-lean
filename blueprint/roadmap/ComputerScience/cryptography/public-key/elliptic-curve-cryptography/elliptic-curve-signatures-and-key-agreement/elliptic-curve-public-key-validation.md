# Elliptic-curve public key validation

Full validation of an elliptic-curve public key $Q$ checks that $Q\ne O$, that its coordinates are canonical field elements satisfying the curve equation, and that $[n]Q=O$; partial validation omits the last check.

Let $T=(p,a,b,G,n,h)$ be valid SEC 1 elliptic-curve domain parameters over a prime field: $E:y^2=x^3+ax+b$ over $\mathbb{F}_p$, $G\in E(\mathbb{F}_p)$ of prime order $n$, cofactor $h=\#E(\mathbb{F}_p)/n$, and in particular $n\nmid h$. For a claimed public key $Q$:

1. reject if $Q=O$;
2. writing $Q=(x_Q,y_Q)$, reject unless $x_Q,y_Q$ are integers in $[0,p-1]$ with $y_Q^2\equiv x_Q^3+ax_Q+b\pmod p$;
3. reject unless $[n]Q=O$;
4. otherwise accept.

*Partial validation* performs steps 1, 2 and 4 and so accepts exactly the affine points of $E(\mathbb{F}_p)$; *full validation* performs all steps and accepts exactly the points of $\langle G\rangle\setminus\{O\}$. When $h=1$, step 3 is implied by steps 1–2 because every point of $E(\mathbb{F}_p)$ then has order dividing $n$. For a twisted Edwards curve $ax^2+y^2=1+dx^2y^2$, NIST SP 800-186 accepts in partial validation every affine point of the curve, including the identity $(0,1)$, and full validation additionally rejects $(0,1)$ and checks $[n]Q=(0,1)$. Full validation certifies that $Q\in\langle G\rangle\setminus\{O\}$; it says nothing about who holds the corresponding private key.

## Depends on

None.

## Proof depends on

None.

## Expansion

Since $\#E(\mathbb{F}_p)=hn$ with $n$ prime and $n\nmid h$, the points killed by $n$ form the unique subgroup of order $n$, which is $\langle G\rangle$; so step 3 together with steps 1–2 characterizes $\langle G\rangle\setminus\{O\}$. Without $n\nmid h$ this fails: over $\mathbb{F}_5$ the curve $y^2=x^3+x$ has four points, $G=(0,0)$ and $Q=(2,0)$ both have order $2$, and $Q\notin\langle G\rangle$. The case $h=1$ is Lagrange's theorem. Full validation rejects every point outside $\langle G\rangle\setminus\{O\}$, which excludes the small-subgroup and related attacks in which a party is made to compute with such a point.

## Sources

- Certicom Research, *SEC 1: Elliptic Curve Cryptography*, Standards for Efficient Cryptography, version 2.0, 2009, <https://www.secg.org/sec1-v2.pdf>, Sections 3.1.1, 3.2.2, 3.2.2.1, 3.2.3 and 3.2.3.1.
- L. Chen, D. Moody, K. Randall, A. Regenscheid and A. Robinson, *Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve Domain Parameters*, NIST SP 800-186, 2023, doi:10.6028/NIST.SP.800-186, Appendix D.1.1–D.1.3.
