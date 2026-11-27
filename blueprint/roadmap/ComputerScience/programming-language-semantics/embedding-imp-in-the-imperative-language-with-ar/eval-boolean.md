# Translated Boolean expressions are true exactly when IMP evaluates them to true

For every renaming $\rho$ from natural numbers to strings, IMP Boolean expression $b$ and state $s$ of the imperative language with arrays: the translation of $b$ is true in $s$ if and only if $b$ evaluates to the Boolean value true in the projected IMP state $\pi_\rho(s)$. No injectivity of $\rho$ is needed.
