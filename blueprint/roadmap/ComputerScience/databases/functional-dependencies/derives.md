# Derivability with Armstrong's axioms

Let $F$ be a finite set of functional
dependencies over a set $A$ of attributes. Derivability from $F$ is the least property of
functional dependencies over $A$ such that, for all finite sets $X$, $Y$, $Z$ of attributes:
every dependency of $F$ is derivable; $X \to Y$ is derivable whenever $Y \subseteq X$
(reflexivity); if $X \to Y$ is derivable, then so is $X \cup Z \to Y \cup Z$ (augmentation);
and if $X \to Y$ and $Y \to Z$ are derivable, then so is $X \to Z$ (transitivity).
