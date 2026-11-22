# Separation gives nonaliasing for binder lifting

Let $\Gamma$ be a service environment and $\Delta$ an ownership context separated from $\Gamma$ (no
owned endpoint is named by a declared trigger). Then for every natural number $k$, the lifting
$\uparrow_k$ (which adds one to every variable index $\ge k$ and fixes constants) does not alias
$\Delta$ with $\Gamma$.
