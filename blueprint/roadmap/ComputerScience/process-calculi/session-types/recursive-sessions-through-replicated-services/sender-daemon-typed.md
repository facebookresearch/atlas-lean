# The sender daemon is typed with empty ownership

For every natural number $n$ and polarity $r$, $\Gamma_r; \emptyset \vdash_n D_s$, where $D_s =
{!\mathrm{c}_{710}(\cdot).W_s(\mathrm{v}_0)}$ and $W_s(x) = \overline{x}\langle
\mathrm{c}_{712}\rangle.\overline{\mathrm{c}_{710}}\langle x\rangle.\mathbf{0}$.

The service environment $\Gamma_r$ declares $710 \mapsto (0, r, \kappa)$ and $711 \mapsto (0, \bar
r, \bar\kappa)$ (priority, polarity of the transferred endpoint, capability), where $\kappa =
(7,R)$, $\bar\kappa = (7,\overline{R})$ and $R$ is the cursor at the single node of the one-node
graph whose node sends a name and loops to itself. Finally $\Gamma; \Delta \vdash_n p$ denotes
runtime typing with shared services at depth $n$, service environment $\Gamma$ and ownership context
$\Delta$.
