# Successor criterion for monotone sequences

Let $\alpha$ be a preordered set. A sequence
$f : \mathbb{N} \to \alpha$ is monotone (that is, $f(m) \le f(n)$ whenever $m \le n$)
if and only if $f(n) \le f(n+1)$ for every $n \in \mathbb{N}$.

## Sources

- `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Monotone), "Convergent Sequences of the Real Numbers section", part (1): a sequence is monotone increasing if `xₙ ≤ xₙ₊₁` for all `n`. The v1 formalization `Sequences.monotone_increasing_iff` in `v1/Atlas/RealAnalysis/code/Sequences/Monotone.lean` states this only for `ℝ`-valued sequences; here it is generalized to any preorder `α`.
