# Orthonormal normalization of shifted Jacobi polynomials

For $a,b>0$, let $Q_n^{(a,b)}$ be the canonical
`Polynomial.shiftedJacobi a b n`, normalized by $Q_n(0)=1$:
$Q_n(x)=\sum_{k=0}^n(-1)^k\binom nk(n+a+b-1)_{(k)}x^k/a_{(k)}$.
Here $u_{(k)}=u(u+1)\cdots(u+k-1)$ and $u_{(0)}=1$.
Its positive-leading-coefficient, Beta-orthonormal normalization is

$$R_n^{(a,b)}(x)=(-1)^n c_n\frac{a_{(n)}}{n!}Q_n^{(a,b)}(x),
\qquad c_0=1,\qquad
c_n=\sqrt{\frac{(2n+a+b-1)(a+b)_{(n-1)}n!}{a_{(n)}b_{(n)}}}
\quad(n\ge1).$$

The separate value at $n=0$ includes $a+b=1$; no negative-index
rising factorial is needed. Equivalently
$R_n(x)=c_nP_n^{(b-1,a-1)}(2x-1)$ in the classical Jacobi convention.
For $Y\sim\mathrm{Beta}(a,b)$,
$\mathbb E[R_m(Y)R_n(Y)]=\delta_{mn}$.
The unnormalized weight is $x^{a-1}(1-x)^{b-1}$; its integral is
$B(a,b)$, so orthonormality is with respect to the **probability** weight.

The polynomials satisfy

$$x(1-x)R_n''+(a-(a+b)x)R_n'=-n(n+a+b-1)R_n.$$

For example $R_0=1$ and
$R_1(x)=\sqrt{(a+b+1)/(ab)}\,((a+b)x-a)$.
For $a=b=1$, $R_n(x)=\sqrt{2n+1}\,P_n(2x-1)$ with classical Legendre
$P_n$. For $a=b=2$, $R_n$ is
$(-1)^n\sqrt{2(2n+3)/(3(n+1)(n+2))}\,C_n^{(3/2)}(1-2x)$.
In particular
$\int_0^1x(1-x)C_n^{(3/2)}(1-2x)^2\,dx=(n+1)(n+2)/(4(2n+3))$.

## Expansion

The underlying facts are the standard ones for shifted Jacobi polynomials
on $[0,1]$: their differential equation, orthogonality with respect to the
Beta weight, the norms (including degree zero), the value at one in the
case $a=b=1$, and the relation to Gegenbauer polynomials of index $3/2$.
This page fixes the normalization that connects them.
For $n\ge1$, division of the canonical norm by $B(a,b)$ gives
$\mathbb E Q_n(Y)^2=n!b_{(n)}/((2n+a+b-1)(a+b)_{(n-1)}a_{(n)})$;
scaling gives the displayed identities. The ODE is unchanged by scaling.
No graph prerequisite is needed to state this explicit definition.

## Sources

- R. C. Griffiths and D. Spanò, *Diffusion processes and coalescent trees* (2010), <https://arxiv.org/abs/1003.4650>, Section 1, (1.2)–(1.5), for the classical-to-orthonormal normalization. The degree-zero case is stated separately here.
