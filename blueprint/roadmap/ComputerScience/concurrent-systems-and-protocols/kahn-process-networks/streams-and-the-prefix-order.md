# Streams and the prefix order

For a set $D$, let $D^\omega$ be the set of finite or countably infinite sequences of elements of $D$, including the empty sequence $\Lambda$. For $X, Y \in D^\omega$, $X \sqsubseteq Y$ if $X$ is an initial segment of $Y$; this is a partial order with least element $\Lambda$. For partial orders $A$ and $B$ in which every increasing chain has a least upper bound, a map $f : A \to B$ is *continuous* if $f(\lim a) = \lim f(a)$ for every increasing chain $a$ of $A$; a continuous map is monotone.

## Sources

- G. Kahn, "The semantics of a simple language for parallel programming", IFIP Congress 74, 1974; retypeset version read at <https://perso.ensta.fr/~chapoutot/various/kahn_networks.pdf>, Sections 2.2.2 ("Sequence domains") and 2.2.4 ("Continuous mappings").
