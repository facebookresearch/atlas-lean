# Authoritative camera

The *authoritative camera* $\mathrm{AUTH}(M)$ over a unital camera $M$ is defined so that one party owns an exclusive authoritative element $\bullet a$ while others own fragments $\circ b$, validity forcing every fragment to be included in the authoritative element.

$$
\mathrm{AUTH}(M) \triangleq \mathrm{EX}(M)^? \times M, \qquad (x_1, b_1) \cdot (x_2, b_2) \triangleq (x_1 \cdot x_2,\ b_1 \cdot b_2), \qquad |(x, b)| \triangleq (\bot, |b|),
$$

$$
\mathcal{V}(x, b) \triangleq \{ n \mid (x = \bot \land n \in \mathcal{V}(b)) \lor (\exists a.\ x = \mathrm{ex}(a) \land n \in \mathcal{V}(a) \land b \overset{n}{\preccurlyeq} a) \}.
$$

Write $\bullet a \triangleq (\mathrm{ex}(a), \varepsilon)$ and $\circ b \triangleq (\bot, b)$. In this camera $\bullet a \cdot \bullet a'$ is valid at no index, $\circ b \cdot \circ b' = \circ (b \cdot b')$, and $n \in \mathcal{V}(\bullet a \cdot \circ b) \iff n \in \mathcal{V}(a) \land b \overset{n}{\preccurlyeq} a$.

## Depends on

- [Cameras](cameras.md)
- [Exclusive camera](exclusive-camera.md)
- [Option camera](option-camera.md)

## Proof depends on

- [Cameras](cameras.md)
- [Exclusive camera](exclusive-camera.md)
- [Option camera](option-camera.md)

## Expansion

Two authoritative elements compose to $(\mathsf{inv}, \varepsilon)$, valid nowhere; fragments compose in the second component; and $\bullet a \cdot \circ b = (\mathrm{ex}(a), b)$ gives the validity characterisation. These are the three key properties the source names: exclusivity of $\bullet a$, fragments composing as in $M$, and validity tying them together.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 6.3.3 (the authoritative camera AUTH(M), the notations for authoritative and fragmentary elements and its key properties) and Section 7.1.1 (its use over finite maps into AG).
