# Filtered De Rham Source

The filtered relative de Rham complex of the coefficient $M$ (a finite locally free module
over the étale structure sheaf $\mathcal{O}_X$ with a filtration and a connection, for the
differentials $\Omega$ of $f : X \to Y$): a filtered complex of modules over $f^{-1}\mathcal{O}_Y$
(`native`) whose degree-$n$ term is identified with $M \otimes \Omega^n$, where
$\Omega^n = \bigwedge^n \Omega$, as an $f^{-1}\mathcal{O}_Y$-module (`terms`), and which is zero
in negative degrees (`negative_zero`); whose $j$-th filtered piece has degree-$n$ term identified
with the image of $\mathrm{Fil}^{j-n} M \otimes \Omega^n$ in $M \otimes \Omega^n$
(`filtered_terms`), compatibly with the inclusion into the complex (`filtered_source`); and whose
differential $M \otimes \Omega^n \to M \otimes \Omega^{n+1}$ is, on every relative affinoid chart,
the extension of the local connection of $M$ (`differential_source`).
