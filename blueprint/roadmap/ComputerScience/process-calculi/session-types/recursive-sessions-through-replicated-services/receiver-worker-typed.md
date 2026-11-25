# The receiver worker is runtime-typed

Let $n$ be a natural number, $r$ a polarity and $b$ a name scoped at depth $n$ (a constant, or a
variable with index $< n$) with $b \ne \mathrm{c}_{710}$ and $b \ne \mathrm{c}_{711}$. Then
$\Gamma_r; \{b^{\bar r} \mapsto \bar\kappa\} \vdash_n W_r(b)$, where $W_r(b) =
b(\cdot).\overline{\mathrm{c}_{711}}\langle \uparrow_0 b\rangle.\mathbf{0}$.

The service environment $\Gamma_r$ declares $710 \mapsto (0, r, \kappa)$ and $711 \mapsto (0, \bar
r, \bar\kappa)$ (priority, polarity of the transferred endpoint, capability), where $\kappa =
(7,R)$, $\bar\kappa = (7,\overline{R})$ and $R$ is the cursor at the single node of the one-node
graph whose node sends a name and loops to itself. Finally $\Gamma; \Delta \vdash_n p$ denotes
runtime typing with shared services at depth $n$, service environment $\Gamma$ and ownership context
$\Delta$.
