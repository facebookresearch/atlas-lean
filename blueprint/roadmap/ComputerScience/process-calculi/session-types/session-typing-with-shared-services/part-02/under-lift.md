# Binder extension preserves nonaliasing of lifted contexts

Let $\Gamma$ be a service environment, $\Delta$ an ownership context and $f$ a map from names to
names that does not alias $\Delta$ with $\Gamma$. Then $f^{\uparrow}$ does not alias
$\uparrow_0\Delta$ with $\Gamma$, where $\uparrow_0\Delta$ raises every variable name index of an
endpoint by one and $f^{\uparrow}$ is the extension of $f$ under one binder.
