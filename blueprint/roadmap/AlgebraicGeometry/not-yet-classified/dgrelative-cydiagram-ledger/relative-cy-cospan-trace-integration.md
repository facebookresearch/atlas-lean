# Relative cy cospan trace integration

Construction data for composing relative Calabi–Yau cospans (Brav–Dyckerhoff, Theorem 6.2). Let
$k$ be a field and `P` a diagram of DG categories over $k$ consisting of functors $e : A \to X$,
$f : B \to X$, $g : B \to Y$, $h : C \to Y$, $i : X \to Z$ and $j : Y \to Z$ with
$i \circ f = j \circ g$, such that the square formed by $f$, $g$, $i$ and $j$ is a Morita pushout
(for the DG frame system `R`). Let $n \in \mathbb{Z}$, let `S` be a negative cyclic trace system,
and fix bar and duality data `DA`, …, `DZ` (`CYCategoryData`) for the six categories, with $A$, $B$,
$C$, $X$ and $Y$ homologically smooth (no smoothness hypothesis on $Z$). This constructs a
`CospanTraceIntegration` with these data: module data, the cospan operations, the completed coherent
grid diagrams, the cyclic coefficient data and, for every compatible negative cyclic class, the
class-induced maps together with a joint comparison of the dual and shifted grid diagrams,
identified with the class maps pointwise up to homotopy.
