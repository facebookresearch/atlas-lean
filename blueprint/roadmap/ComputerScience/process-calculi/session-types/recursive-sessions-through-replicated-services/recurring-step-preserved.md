# Steps preserve typing at the recurring interface

Let $n$ be a natural number, $r$ a polarity, $b$ a name and $p$, $q$ processes. If $\Gamma_r;
I_{b,r} \vdash_n p$ and $p \to q$, then $\Gamma_r; I_{b,r} \vdash_n q$.

The ownership context $I_{b,r} = \{b^{r} \mapsto \kappa\} \cup \{b^{\bar r} \mapsto \bar\kappa\}$
owns both endpoints of $b$. The service environment $\Gamma_r$ declares $710 \mapsto (0, r, \kappa)$
and $711 \mapsto (0, \bar r, \bar\kappa)$ (priority, polarity of the transferred endpoint,
capability), where $\kappa = (7,R)$, $\bar\kappa = (7,\overline{R})$ and $R$ is the cursor at the
single node of the one-node graph whose node sends a name and loops to itself. Finally $\Gamma;
\Delta \vdash_n p$ denotes runtime typing with shared services at depth $n$, service environment
$\Gamma$ and ownership context $\Delta$.
