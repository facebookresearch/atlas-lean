# Universal-cover splitting for two integrable Kähler tangent summands

Let $X$ be compact and connected complex, Hausdorff and second countable, of complex dimension $n\ge2$, with a Kähler metric (positive Hermitian metric with closed fundamental two-form). Let $P$ be a holomorphic idempotent on $TX$ with range and kernel of positive ranks $r_1,r_2$ everywhere. Assume each of the distributions $P$ and $1-P$ is integrable: on each chart, the Lie bracket of two holomorphic fields fixed by the corresponding projector is fixed by it. Given an ordinary covering map $\pi:Z\to X$ with connected simply connected $Z$, and with the lifted complex structure making $\pi$ a local biholomorphism, there are connected simply connected complex manifolds $Y_j$ of dimensions $r_j$ and a biholomorphism $Z\to Y_1\times Y_2$. Its derivative maps the pullbacks by $d\pi$ of the range and kernel of $P$ onto the first and second tangent factors, respectively. Integrability is a hypothesis for both distributions, not part of the conclusion.

## Depends on

- [Kähler structure](../../AlgebraicGeometry/not-yet-classified/kahler-class-geometry/kahler-structure.md)
- Holomorphic tangent subbundles via projection, chartwise bracket integrability, and ordinary complex covering maps.

## Proof depends on

- Global product theorem for the two transverse holomorphic foliations of the compact Kähler base.

## Expansion

Identify the leaves with the two product factors on the cover, verify connectedness and simple connectedness of both, and track the two pulled-back tangent distributions through the differential.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KahlerSplitting.lean#L124-L134) (statement and local definitions).
