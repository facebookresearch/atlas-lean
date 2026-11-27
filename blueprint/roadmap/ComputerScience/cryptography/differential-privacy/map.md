# Post-processing by a measurable map

If $M$ is $(\varepsilon, \delta)$-differentially private and $f : \Omega \to \Omega'$ is measurable,
then $x \mapsto f_* M(x)$ is $(\varepsilon, \delta)$-differentially private. For an event
$S \subseteq \Omega'$ apply the definition to the preimage $T = f^{-1}(S)$.

## Background

- [Processing cannot increase information](../../../InformationTheory/information-inequalities/data-processing-inequality/measure-mutual-information-map-le.md): the analogous monotonicity for mutual information.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Proposition 2.1, deterministic case of the proof.
