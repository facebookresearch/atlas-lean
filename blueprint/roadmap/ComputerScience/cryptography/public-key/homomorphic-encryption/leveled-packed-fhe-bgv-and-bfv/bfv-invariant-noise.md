# Invariant noise of a BFV ciphertext

The invariant noise of a two-component BFV ciphertext is the rational polynomial $v$ left after scaling the decryption polynomial by $t/q$: $\tfrac tq(c_0+c_1s)=m+v+at$ for an integer polynomial $a$. Decryption is correct when $\|v\|_\infty<1/2$, and $-\log_2(2\|v\|_\infty)$ is the noise budget.

Let $n$ be a power of two, $R=\mathbb{Z}[x]/(x^n+1)$, let $q,t\ge 2$ be the ciphertext and plaintext moduli, and let $s\in R$ be the secret key. Let $\mathrm{ct}=(c_0,c_1)\in R_q^{2}$ encrypt $m\in R_t$. Taking integer representatives of $c_0,c_1$ and $m$, the elements $v\in\mathbb{Q}[x]/(x^n+1)$ with

$$
\frac{t}{q}\,\mathrm{ct}(s)=\frac{t}{q}\,(c_0+c_1s)=m+v+at\qquad\text{for some }a\in R
$$

form a coset $v_0+tR$, independent of the representatives chosen. The *invariant noise* of $\mathrm{ct}$ is an element of this coset of smallest infinity norm; its norm $\|v\|_\infty$ is well defined, and the coefficientwise representative in $[-t/2,t/2)$ is a canonical choice. For $v\ne 0$ the *noise budget* is $-\log_2(2\|v\|_\infty)$, and it is $+\infty$ when $v=0$.

Decryption outputs $\bigl[\lfloor\tfrac tq[c_0+c_1s]_q\rceil\bigr]_t$. If $\|v\|_\infty<\tfrac12$, equivalently the noise budget is positive, the output equals $m$ in $R_t$. The condition is sufficient, not necessary.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Proof depends on

None.

## Expansion

Changing a representative of $c_i$ by a multiple of $q$, or of $m$ by a multiple of $t$, changes $v$ by an element of $tR$, which gives the coset statement. For decryption, write $[c_0+c_1s]_q=c_0+c_1s+Aq$ with $A\in R$; then $\tfrac tq[c_0+c_1s]_q=m+v+(a+A)t$, and when every coefficient of $v$ has absolute value below $1/2$, rounding removes $v$ and reduction modulo $t$ removes $(a+A)t$. In contrast with the inherent noise $v'$ of $[\mathrm{ct}(s)]_q=\Delta[m]_t+v'$, whose threshold depends on $\Delta$, the threshold for the invariant noise is $1/2$.

## Sources

- Anamaria Costache, Kim Laine, Rachel Player, "Evaluating the Effectiveness of Heuristic Worst-Case Noise Analysis in FHE", Computer Security – ESORICS 2020, Lecture Notes in Computer Science, Springer (2020), DOI [10.1007/978-3-030-59013-0_27](https://doi.org/10.1007/978-3-030-59013-0_27): §2.1, pp. 4–5 (power-of-two $n$), §4.1, Definition 3 (FV invariant noise, p. 10) and the following correctness requirement $\|v\|<\tfrac12$ (p. 11), and the FV noise budget $-\log_2(2\cdot\|v\|)$ in §3.2 (p. 9, paragraph after Definition 2) and §4.2 (p. 12); read in the [authors' repository copy](https://raw.githubusercontent.com/rachelplayer/CLP19-code/master/2019-493.pdf) of IACR ePrint 2019/493 (28 pages, PDF dated January 28, 2020). The value $+\infty$ at $v=0$ is this page's convention.
