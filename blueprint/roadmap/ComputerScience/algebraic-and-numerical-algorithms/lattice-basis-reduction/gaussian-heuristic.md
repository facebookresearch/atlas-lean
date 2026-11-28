# The Gaussian heuristic for lattice point counts

The Gaussian heuristic predicts that a nice region $S$ contains about $\operatorname{vol}(S)/\operatorname{vol}(L)$ points of a full-rank lattice $L\subset\mathbb{R}^n$; applied to balls it predicts a shortest nonzero vector of length $\operatorname{GH}(L)=\operatorname{vol}(L)^{1/n}V_n(1)^{-1/n}$. It is a model, not a theorem.

Let $n\ge1$, let $L\subset\mathbb{R}^n$ be a lattice of rank $n$ with covolume $\operatorname{vol}(L)>0$, and let $V_n(1)=\pi^{n/2}/\Gamma(n/2+1)$ be the volume of the Euclidean unit ball. The *Gaussian heuristic* is the prediction that, for a "nice" measurable set $S\subset\mathbb{R}^n$,

$$
\#(S\cap L)\approx \frac{\operatorname{vol}(S)}{\operatorname{vol}(L)} .
$$

Applied to balls of radius $r$, of volume $r^nV_n(1)$, it predicts

$$
\lambda_1(L)\approx \operatorname{GH}(L) := \operatorname{vol}(L)^{1/n}\,V_n(1)^{-1/n}.
$$

"Nice" is not made precise, and the prediction is not valid for every lattice or every set. A rigorous companion bound holds for every lattice of rank $n$: $\lambda_1(L)\le 2\operatorname{GH}(L)$. Concrete lattice attacks use the heuristic to predict, for instance, the second minimum of an embedding lattice or the lengths found by enumeration.

## Proof sketch

The companion bound follows from Minkowski's convex body theorem, which needs strict volume inequality: for every $r>2\operatorname{GH}(L)$ the ball of radius $r$ is convex, symmetric and has volume $r^nV_n(1)>2^n\operatorname{vol}(L)$, so it contains a nonzero lattice vector; hence $\lambda_1(L)<r$ for all such $r$, and $\lambda_1(L)\le2\operatorname{GH}(L)$. Chen and Nguyen state the bound and the heuristic; the heuristic itself has no proof.

## Depends on

- [Shortest vector, independent vectors and guaranteed distance decoding problems](../../cryptography/public-key/lattice-and-code-based-cryptography/lattice-gaussians-and-smoothing-parameter/svp-sivp-givp-and-gdd.md)

## Proof depends on

- [Minkowski's convex body theorem](../../../NumberTheory/diophantine-approximation/uniform-distribution-metric/minkowski-convex-body-theorem.md)

## Sources

- Yuanmi Chen, Phong Q. Nguyen, "BKZ 2.0: Better Lattice Security Estimates", ASIACRYPT 2011, Lecture Notes in Computer Science 7073, pp. 1–20, [https://www.iacr.org/archive/asiacrypt2011/70730001/70730001.pdf](https://www.iacr.org/archive/asiacrypt2011/70730001/70730001.pdf), Section 2, Equation (1) and the Minkowski remark that follows it.
- Martin R. Albrecht, Florian Göpfert, Fernando Virdia, Thomas Wunderer, "Revisiting the Expected Cost of Solving uSVP and Applications to LWE", ASIACRYPT 2017, Lecture Notes in Computer Science 10624; IACR ePrint 2017/815, [https://eprint.iacr.org/2017/815](https://eprint.iacr.org/2017/815), Section 3.1 (second minimum modelled by the Gaussian heuristic).
- Martin R. Albrecht, Shi Bai, Pierre-Alain Fouque, Paul Kirchner, Damien Stehlé, Weiqiang Wen, "Faster Enumeration-based Lattice Reduction: Root Hermite Factor $k^{1/(2k)}$ in Time $k^{k/8+o(k)}$", CRYPTO 2020, Lecture Notes in Computer Science 12171, [https://iacr.org/archive/crypto2020/12171096/12171096.pdf](https://iacr.org/archive/crypto2020/12171096/12171096.pdf), Section 2.1 (Gaussian heuristic $\mathrm{GH}(L)=v_n^{-1/n}\operatorname{vol}(L)^{1/n}$ and Minkowski's bound).
