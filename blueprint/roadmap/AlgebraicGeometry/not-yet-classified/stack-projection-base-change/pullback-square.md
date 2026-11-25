# Pullback Square

Base change for the projections $p : R \to X$ and $q : R_Y \to Y$, where $R_Y$ is the
restriction of $R$ along $f : Y \to X$, and $X$ and $Y$ are represented by the models $S$ and $T$,
whose quasi-coherent modules the dictionaries $K$ and $L$ identify with those on the schemes: a
natural isomorphism $\mathrm{res} \circ p^* \cong q^* \circ f^*$ of functors from quasi-coherent
modules on $X$ to quasi-coherent modules on $R_Y$, where $\mathrm{res}$ restricts modules from $R$
to $R_Y$ (`comparison`), which on sections is the canonical isomorphism
$(f \circ t)^* N \cong t^* f^* N$: for every quasi-coherent module $N$ on $X$, every affine point
of $R_Y$, with base map $t$ to $Y$, and every section $x$ over that point, the global section of
$t^* f^* N$ that `targetValue` attaches to the image of $x$ under the comparison is the image under
this isomorphism of the global section of $(f \circ t)^* N$ that `sourceValue` attaches to $x$
(`normalization`).
