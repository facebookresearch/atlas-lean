# Hartogs' theorem on separate analyticity

Let $n \in \mathbb{N}$ and let
$f : \mathbb{C}^n \to \mathbb{C}$ be such that for every point $x \in \mathbb{C}^n$ and every
coordinate $i$, the function $z \mapsto f(x_1, \dots, x_{i-1}, z, x_{i+1}, \dots, x_n)$ is
complex differentiable on all of $\mathbb{C}$. Then $f$ is complex differentiable on all of
$\mathbb{C}^n$.

No continuity or boundedness of $f$ is assumed.

Proof: induction on the number of variables. Baire category gives a polydisc where $f$ is
bounded, where Osgood's lemma makes it holomorphic; Hartogs' lemma on sub-mean-value functions
then makes the Cauchy expansion in the last variable converge locally uniformly.

## Sources

- Hartogs separate analyticity (Osgood–Hartogs); see Hörmander; Lean is scalar-valued entire separately holomorphic via Function.update slices implies jointly Differentiable ℂ, finite-dimensional ℂⁿ specialization.
