# Universal approximation by linear functionals of the signature

Fix $a < b$ and $d \ge 0$. Describe an absolutely continuous path
$X : [a, b] \to \mathbb{R}^{d+1}$ with a fixed starting point by its velocity
$f \in L^1([a,b]; \mathbb{R}^{d+1})$; the $L^1$ distance of velocities is then the
bounded-variation distance $|X_a - Y_a| + \int_a^b |\dot X_t - \dot Y_t|\,dt$ of the paths.
Suppose the first coordinate is time, $f_0 = 1$ almost everywhere. Let $K$ be a compact set of
such velocities and $g$ a real function continuous on $K$. Then for every $\varepsilon > 0$
there are finitely many reals $\lambda_1, \dots, \lambda_n$ and words $I_1, \dots, I_n$ with

$$\Big|\, g(X) - \sum_{k=1}^{n} \lambda_k\, S(X)^{I_k}_{a,b} \Big| < \varepsilon \qquad \text{for every } X \in K .$$

This is the theoretical basis of the signature method in machine learning: a continuous
function of a stream is approximately linear in the signature of the time-augmented stream.

The time coordinate is needed: without it the signature does not separate paths that differ by
reparametrisation or by tree-like pieces (see
[tree-like paths](../tree-like-paths-and-uniqueness-of-the-signature/README.md)).

## Informally uses

- [Shuffle product identity (Ree)](signature-mul-signature.md): linear functionals of the
  signature form an algebra, as the Stone–Weierstrass theorem requires.

## Background

- [Signature along a repeated letter](signature-replicate.md): with time as letter $0$,
  $S^{0 \cdots 0\, i}_{a,b} = \int_a^b \frac{(t-a)^k}{k!}\, \dot X^i_t\, dt$ are the moments of
  $\dot X^i_t\,dt$; this is how the source shows that the signature separates the points of $K$
  (its Proposition 1.34).
- [Universal approximation theorem](../../approximation-theory/universal-approximation.md):
  the corresponding density theorem for neural networks on compact subsets of $\mathbb{R}^n$.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Propositions 1.34 and 1.35 (the norm on paths is the bounded-variation
  norm $|X_a| + \int_a^b |\dot X_t|\,dt$, and the proof uses the Stone–Weierstrass theorem,
  their Theorem 1.33).
- T. Lyons, *Rough paths, signatures and the modelling of functions on streams*, Proc. ICM 2014,
  arXiv:1405.4537, Lemma 9.4.
