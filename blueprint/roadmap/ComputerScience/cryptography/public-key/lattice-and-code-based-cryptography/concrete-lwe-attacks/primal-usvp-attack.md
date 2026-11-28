# Primal attack on LWE through Kannan's embedding

The primal attack embeds $m$ LWE samples and an integer embedding factor $t$ into an $(m+1)$-dimensional $q$-ary lattice that contains $(\bar e,t)$, with $\bar e$ the centred lift of the error, then runs BKZ hoping to find this vector. The 2016 estimate predicts success with block size $\beta$ when $\sqrt\beta\,\sigma\le\delta_0^{2\beta-d}\operatorname{vol}(\Lambda)^{1/d}$; it is a heuristic.

Let $(A,c)$ with $c\equiv As+e \pmod q$ be $m>n$ LWE samples whose errors have standard deviation $\sigma$, and let $\bar e\in\mathbb{Z}^m$ be the representative of $e$ with entries in $(-q/2,q/2]$. Assume that after a permutation of the $m$ samples, applied to the rows of $A$ and to the entries of $c$ and $e$ alike, $A=\binom{A_1}{A_2}$ with $A_1\in\mathbb{Z}_q^{n\times n}$ invertible modulo $q$ (this can fail with noticeable probability for small $q$, e.g. $q=2$, $m=n+1$). Put $A'=(A_2A_1^{-1})^{\mathsf T}\in\mathbb{Z}_q^{n\times(m-n)}$, so that $A_1^{-\mathsf T}A^{\mathsf T}=[I_n\mid A']$.

**Kannan's embedding** with an integer factor $t\ge1$ is the lattice $\Lambda\subset\mathbb{Z}^{m+1}$ spanned by the rows of

$$
\begin{pmatrix} I_n & A' & 0\\ 0 & qI_{m-n} & 0\\ c^{\mathsf T} & & t\end{pmatrix},
$$

with entries of $A'$ and $c$ taken as integer representatives and the last row $(c^{\mathsf T},t)$. It has dimension $d=m+1$, volume $t\,q^{m-n}$, and contains $(\bar e,t)$. When $\sqrt{\|\bar e\|^2+t^2}$ is much smaller than both $q$ (the lattice contains vectors of norm $q$ with last coordinate $0$) and the Gaussian-heuristic length, $(\bar e,t)$ is expected to be the unique shortest vector up to sign; in practice $t=1$.

**Attack and 2016 estimate.** Run BKZ with block size $\beta$ on this basis. Albrecht, Göpfert, Virdia and Wunderer, following Alkim, Ducas, Pöppelmann and Schwabe and assuming the geometric series assumption, predict that the short vector is found when

$$
\sqrt{\beta}\,\sigma\ \le\ \delta_0^{\,2\beta-d}\,\operatorname{vol}(\Lambda)^{1/d},
$$

because the projection of the short vector orthogonally to the first $d-\beta$ Gram–Schmidt vectors, of expected length about $\sqrt\beta\,\sigma$, is then shorter than the predicted $\|b^*_{d-\beta+1}\|$. Their experiments with Kannan's embedding and $t=1$ behave as this estimate predicts, somewhat better; the estimate remains a heuristic, not a theorem.

## Expansion

Volume: the basis is triangular with diagonal $1^n,q^{m-n},t$. Membership: put $s'=A_1s\in\mathbb{Z}_q^n$; then $As=\binom{s'}{A_2A_1^{-1}s'}$, so $c^{\mathsf T}\equiv s'^{\mathsf T}[I_n\mid A']+e^{\mathsf T}\pmod q$. Choose the integer vector $\hat s$ with $\hat s_i=c_i-\bar e_i$ for $i\le n$ (a lift of $s'_i$, since $c_i\equiv s'_i+e_i$). The vector $(c^{\mathsf T},t)-\sum_{i\le n}\hat s_i\,(\text{row }i)$ has first $n$ entries exactly $\bar e_1,\dots,\bar e_n$ and entries $n+1,\dots,m$ congruent to $\bar e_{n+1},\dots,\bar e_m$ modulo $q$; subtracting integer multiples of the rows $(0,qI_{m-n},0)$ makes them equal, which gives $(\bar e,t)$. AGVW note (footnote 7) that the exponent printed in the 2016 paper, $2\beta-d-1$, seems to be an error, and use $2\beta-d$. For short secrets the Bai–Galbraith embedding uses the $(n+m+1)$-dimensional lattice containing $(\nu s,e,1)$ (HE Standard, Section 2.1.2); it is a different construction.

## Depends on

- [LWE with a prescribed secret distribution](../small-and-sparse-secret-lwe/lwe-with-a-secret-distribution.md)
- [The block Korkine–Zolotarev (BKZ) reduction algorithm](../../../../algebraic-and-numerical-algorithms/lattice-basis-reduction/bkz-algorithm.md)
- [Root-Hermite factor and the geometric series assumption](../../../../algebraic-and-numerical-algorithms/lattice-basis-reduction/root-hermite-factor-and-geometric-series-assumption.md)
- [The Gaussian heuristic for lattice point counts](../../../../algebraic-and-numerical-algorithms/lattice-basis-reduction/gaussian-heuristic.md)

## Proof depends on

None.

## Sources

- Martin R. Albrecht, Florian Göpfert, Fernando Virdia, Thomas Wunderer, "Revisiting the Expected Cost of Solving uSVP and Applications to LWE", ASIACRYPT 2017, Lecture Notes in Computer Science 10624; IACR ePrint 2017/815, [https://eprint.iacr.org/2017/815](https://eprint.iacr.org/2017/815), Section 1, Equation (1), Section 3.2, Equation (2) and footnote 7, Section 4.
- Martin Albrecht, Melissa Chase, Hao Chen, Jintai Ding, Shafi Goldwasser, Sergey Gorbunov, Shai Halevi, Jeffrey Hoffstein, Kim Laine, Kristin Lauter, Satya Lokam, Daniele Micciancio, Dustin Moody, Travis Morrison, Amit Sahai, Vinod Vaikuntanathan, "Homomorphic Encryption Standard", in Protecting Privacy through Homomorphic Encryption, Springer, 2021, pp. 31–62; IACR ePrint 2019/939, [https://eprint.iacr.org/2019/939](https://eprint.iacr.org/2019/939), Section 2.1.2 a.
