# Mixing implies ergodicity

A mixing transformation $T$ of a probability space $(X, \mu)$ is ergodic. Indeed, if $E$ is a measurable set
with $T^{-1} E = E$, then $T^{-n} E = E$ for every $n$, so the mixing property applied to $A = B = E$ gives

$$\mu(E) = \mu(E \cap T^{-n} E) \longrightarrow \mu(E)^2,$$

hence $\mu(E) = \mu(E)^2$ and $\mu(E) \in \{0, 1\}$. It suffices to treat sets that are invariant in this strict
sense ($T^{-1} E = E$ exactly, not only up to a null set).

The converse fails: an irrational rotation of the circle is ergodic but not mixing. Applied to powers of
$T$, the same argument shows that [mixing maps are totally ergodic](ergodic-iterate.md).

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Proposition 1.2 and its proof.
