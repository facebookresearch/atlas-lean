# From taming to compatibility on closed four-manifolds

Let $X$ be a compact connected Hausdorff second-countable smooth real four-manifold without boundary. Let $J:TX\to TX$ be a smooth real-linear bundle endomorphism with $J_x^2=-1$ at each point. Assume a smooth closed nondegenerate real two-form $\alpha$ with $\alpha(v,Jv)>0$ for all nonzero tangent vectors. Then there is a smooth closed nondegenerate two-form $\eta$ with $\eta(v,Jv)>0$ for all nonzero $v$ and $\eta(Ju,Jv)=\eta(u,v)$ for all tangent vectors $u,v$ at every point. Both forms are tested for smoothness and closure on pullbacks by smooth maps from open sets in $\mathbb R^4$. The conclusion has the same $J$ and does not prescribe a cohomology class or assume integrability.

## Depends on

- [Exterior derivative model](weinstein-conjecture/is-exterior-derivative.md)
- Smooth alternating tangent forms, pullback closure, fibrewise nondegeneracy, smooth almost-complex structures.

## Proof depends on

- Construction of a closed positive $J$-invariant form under the taming hypothesis.

## Expansion

Identify the chartwise and intrinsic exterior derivatives, then factor the construction so the closure, $J$-invariance and strict positivity are proved for the same form.

## Sources

- OpenAI Math, [`taming_implies_compatibility`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TamingCompatibility.lean#L58-L64) (statement and local definitions).
