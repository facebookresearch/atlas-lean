# Flat harmonic kernel polystable

Part of the nonabelian Hodge correspondence: let $M$ be a compact, connected, nonempty,
Hausdorff, second-countable complex manifold modelled on $\mathbb{C}^n$ (smooth as a real
manifold) with a Kähler form $\eta$, and let $A$ be a flat connection on a smooth complex vector
bundle $B$ on $M$ whose local system of horizontal sections is semisimple
(`SemisimpleHorizontals`) and which is pluriharmonic for a Hermitian metric $h$
(`IsPluriharmonic`). Then the holomorphic Higgs sheaf of $(B, h, A)$ (`K.object`: the sections
killed by the $(0,1)$-part of the $h$-unitary part of $A$, with the Higgs field of the harmonic
Higgs model `H`) is polystable with respect to $\eta$, slopes being computed from the
determinant degree data `D` and the coordinate integral given by `R` and `P`. We assume the local
calculus, gluing, sheafification and integration properties of the functions, sections and forms
on $M$ used to define these objects.
