# Cotangent Differential

The cotangent differential of a morphism of prestacks $f : X \to Y$ over $k$, relative to the
chosen representation `C`, by $f^*L_Y$, of the deformations of $Y$ along $f$ (`DF`); here $f^*L_Y$
is the image under the DG pullback model `PB` of the cotangent object $L_Y$ of `CY`. It consists of
a closed degree-zero morphism $df : f^*L_Y \to L_X$ to the cotangent object $L_X$ of `CX`, the
precomposition with $df$ on left slices of the DG nerve (`SlicePrecomposition`), and an edge, in
the mapping space over the coefficient tests, from precomposition with $df$ followed by `C` to the
representation of the derivations of $X$ by $L_X$ followed by the map `m` from derivations of $X$
to deformations of $Y$ along $f$: $df$ is the Yoneda transpose of the map induced by $f$.
