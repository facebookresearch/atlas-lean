# Local truncation of two-party additive shares

Let $x\in\mathbb{Z}_{2^\ell}$ represent an integer of absolute value at most $2^{\ell_x}$ with $\ell>\ell_x+1$, shared as $x_0=x+r$, $x_1=-r$ with $r$ uniform. If each share is truncated by $\ell_D\le\ell_x$ bits locally, the reconstructed residue is the truncation of $x$ up to $\pm1$ modulo $2^\ell$, except with probability at most $2^{\ell_x+1-\ell}$.

All values below are residues modulo $2^\ell$, each identified with its representative in $[0,2^\ell)$. Let $x\in[0,2^{\ell_x}]\cup[2^\ell-2^{\ell_x},2^\ell)$, $r$ uniform in $\mathbb{Z}_{2^\ell}$, $x_0=x+r$ and $x_1=-r$. Define the target $\lfloor x\rfloor=\lfloor x/2^{\ell_D}\rfloor$ if $x\le2^{\ell_x}$ and $\lfloor x\rfloor=(2^\ell-\lfloor(2^\ell-x)/2^{\ell_D}\rfloor)\bmod2^\ell$ otherwise. The parties set, without interaction,

$$
\tilde x_0=\lfloor x_0/2^{\ell_D}\rfloor,\qquad \tilde x_1=\big(2^\ell-\lfloor(2^\ell-x_1)/2^{\ell_D}\rfloor\big)\bmod2^\ell ,
$$

where in $2^\ell-x_1$ the representative $x_1=0$ is read as $2^\ell$. Then, with probability at least $1-2^{\ell_x+1-\ell}$ over $r$,

$$
\tilde x_0+\tilde x_1\equiv\lfloor x\rfloor+e\pmod{2^\ell}\quad\text{for some }e\in\{-1,0,1\};
$$

the statement holds whenever $2^{\ell_x}\le r<2^\ell-2^{\ell_x}$.

## Depends on

- [Additive $n$-out-of-$n$ secret sharing](../../signatures-and-protocols/secure-multiparty-computation/secret-sharing-schemes/additive-secret-sharing.md)

## Proof depends on

None.

## Expansion

Write $r=r_12^{\ell_D}+r_2$ and $x=x_12^{\ell_D}+x_2$ (or $x=2^\ell-x_12^{\ell_D}-x_2$ in the negative case) with $0\le r_2,x_2<2^{\ell_D}$. For $r$ in the stated interval, $x+r$ does not wrap (positive case) or wraps exactly once (negative case), and the reconstruction differs from the target only by the carry between the low parts. The interval's complement has $2^{\ell_x+1}$ values of $r$, which bounds the failure probability; the actual failure event is contained in it. For example $\ell=4$, $\ell_x=2$, $\ell_D=1$, $x=15$, $r=5$ gives $\tilde x_0=2$, $\tilde x_1=14$ and target $0$, all modulo $16$.

## Sources

- Payman Mohassel, Yupeng Zhang, "SecureML: A System for Scalable Privacy-Preserving Machine Learning", IEEE Symposium on Security and Privacy 2017, DOI 10.1109/SP.2017.12, [conference copy](https://www.ieee-security.org/TC/SP2017/papers/466.pdf), §IV-A, Theorem 1 (PDF p. 7) and Appendix B (PDF p. 17).
