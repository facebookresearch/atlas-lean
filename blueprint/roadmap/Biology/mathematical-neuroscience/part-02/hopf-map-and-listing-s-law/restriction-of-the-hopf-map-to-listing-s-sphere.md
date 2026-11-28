# Restriction of the Hopf map to Listing's sphere

**Setting.** Identify rotations of the eye with unit quaternions $a \in S^3 \subset \mathbb{H} = \mathrm{span}(1, i, j, k)$, acting on imaginary quaternions $x$ by $\mathrm{Ad}_a x = a x \bar a$. Let $i$ be the primary gaze direction and $S_E^2$ the unit sphere of imaginary quaternions (possible gaze directions). The *Hopf map* is

$$\chi : S^3 \to S_E^2, \qquad \chi(a) = a\,i\,\bar a,$$

the gaze direction after rotation $a$. *Listing's sphere* is the great 2-sphere $S_L^2 = S^3 \cap \mathrm{span}(1, j, k)$: orientations obtained from the primary position by rotations about axes orthogonal to $i$ (Listing's law). Its equator is $S_L^1 = S^3 \cap \mathrm{span}(j, k)$, and $S_L^+$ is the open hemisphere containing $1$. Every $a \in S_L^2 \setminus \{\pm 1\}$ can be written uniquely as $a = e^{tp} = \cos t + \sin t\,p$ with $p \in S_L^1$ and $0 < t < \pi$.

**Theorem 1.** The restriction $\chi : S_L^2 \to S_E^2$ is a branched $\mathbb{Z}_2$-covering. Precisely:

1. $\chi(\pm 1) = i$ and $\chi(S_L^1) = \{-i\}$;
2. for $p \in S_L^1$, $\chi(e^{tp}) = R_p^{2t}\,i = \cos 2t\,i + \sin 2t\,q$ with $q = p\,i$, so $\chi$ maps the meridian $\{e^{tp}\}$ of Listing's sphere onto the meridian of $S_E^2$ through $q$ as a $\mathbb{Z}_2$-covering ($t \mapsto 2t$ in arc length), and is a diffeomorphism on the half-meridian inside $S_L^+$ (the source's Theorem 1(ii) prints "onto the meridian $S^1_p$ of the Euclidean sphere $S^2_E$ through the point $p\in S^1_E$"; the page writes $q = p\,i$ because $p \perp i$ gives $\mathrm{Ad}_{e^{tp}}\,i = e^{tp}\,i\,e^{-tp} = e^{2tp}\,i$, whose imaginary part off $i$ is $\sin 2t\,p\,i$, and $p\,i \ne \pm p$);
3. more generally, let $\gamma$ be the geodesic (great circle) of Listing's sphere $S_L^2$ through two distinct points of $S_L^+$, let $p \in S_L^1$ be its first point on the equator and $m$ its point of maximal latitude, and write it canonically as $\gamma(t) = \cos t\,p + \sin t\,m = e^{tv}p$ with $v = m\bar p \in S_E^2$; then $\chi(e^{tv}p) = R_v^{2t}(-i)$, so $\chi$ maps $\gamma$ onto the circle obtained by rotating $-i$ about the axis $v$;
4. the restriction $\chi : S_L^+ \to S_E^2 \setminus \{-i\}$ is a diffeomorphism.

## Expansion

For a unit imaginary quaternion $p$ the one-parameter subgroup $e^{tp}$ acts on imaginary quaternions as rotation about $p$ by angle $2t$, so $\chi(e^{tp}) = R_p^{2t} i$. When $p \perp i$, rotating $i$ about $p$ traces the great circle through $i$ and $p\,i$, giving the formula in (2); at $t = \pi/2$, $e^{tp} = p$ and $p\,i\,\bar p = -p\,i\,p = i\,p\,p = -i$, since $p$ and $i$ anticommute and $p^2 = -1$. Thus the whole equator collapses to $-i$ and both poles go to $i$, while the open hemisphere $0 \le t < \pi/2$ covers every other gaze direction exactly once. Statement (4) is the geometric content of Donders' and Listing's laws: for every gaze direction other than straight backward there is exactly one admissible eye orientation, the one reached from the primary position by a single rotation about an axis in Listing's plane. The paper uses this to describe microsaccades and drifts as curves on $S_L^+$ and their images under $\chi$.

## Sources

- D. Alekseevsky, "Microsaccades, Drifts, Hopf Bundle and Neurogeometry", Journal of Imaging 8 (2022) 76, Lemmas 1–2, the canonical parametrization of geodesics of Listing's sphere and Theorem 1 (Section 3.3), <https://doi.org/10.3390/jimaging8030076>, PMCID PMC8953095.
