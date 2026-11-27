# Positive feedback vertex set bound on steady states of sigmoidal ODEs

**Setting.** A continuous model is an ODE $\bar x'=D(\bar f(\bar x)-\bar x)$ with $D$ a positive diagonal matrix and $\bar f:[0,1]^N\to[0,1]^N$ continuous; a multistate (multivalued, finite dynamical) network is a map $f:\mathcal{S}\to\mathcal{S}$, $\mathcal{S}=\prod_{j=1}^N\{0,1,\dots,m_j\}$, iterated as $x(t+1)=f(x(t))$. For each $j$ fix thresholds $0<k^j_1<\dots<k^j_{m_j}<1$ and associate to the level $\ell$ the interval $[\ell]=]k^j_\ell,k^j_{\ell+1}[$ (with $[0]=[0,k^j_1[$ and $[m_j]=]k^j_{m_j},1]$); for $x\in\mathcal{S}$ the **region** is $[x]=[x_1]\times\dots\times[x_N]\subseteq[0,1]^N$.

The **wiring diagram** has vertices $1,\dots,N$ and a signed edge $j\to i$ when $f_i$ depends on $x_j$ (positive if $f_i$ is increasing in $x_j$, negative if decreasing). A **positive feedback vertex set** (PFVS) is a set $P$ of vertices meeting every positive feedback loop.

**Theorem (discrete bound; Veliz-Cuba et al., Theorem 4.1, due to Aracena for Boolean and Richard for multivalued networks).** If $P$ is a PFVS of the wiring diagram of $f$, then $f$ has at most $\prod_{i\in P}(m_i+1)$ fixed points; in the Boolean case at most $2^{|P|}$.

**Theorem (continuous bound; Veliz-Cuba et al., Theorem 4.2).** Under the hypotheses of the steady-state correspondence theorem (uniform convergence of $\bar f^n$ on compact subsets of each region to a point of $[f(x)]$), for $n$ large enough the number of steady states in $K$ of $\bar x'=D(\bar f^n(\bar x)-\bar x)$ is at most $\prod_{i\in P}(m_i+1)$, where $P$ is a PFVS of the wiring diagram, and the exceptional set $[0,1]^N\setminus K$ can be made of arbitrarily small Lebesgue measure.

For example, a nine-variable Hill-type network whose positive loops all pass through a single node has at most $2$ steady states (all stable) in $K$ for large Hill exponents.

## Depends on

- [Steady-state correspondence between sigmoidal ODEs and multistate networks](steady-state-correspondence-between-sigmoidal-odes-and-multistate-networks.md)

## Proof sketch

The correspondence theorem identifies the ODE steady states in $K$ bijectively with fixed points of $f$, so any combinatorial bound on fixed points of the multistate network transfers to the ODE. Positive feedback loops are necessary for multistationarity; once every such loop is cut by $P$, the values on $P$ determine a fixed point, giving the product bound.

## Sources

- Alan Veliz-Cuba, Joseph Arthur, Laura Hochstetler, Victoria Klomps and Erikka Korpi, "On the Relationship of Steady States of Continuous and Discrete Models Arising from Biology", *Bulletin of Mathematical Biology* 74 (2012), 2779–2792, <https://doi.org/10.1007/s11538-012-9778-1>. Preprint version: arXiv:1109.5197 (2011), <https://doi.org/10.48550/arXiv.1109.5197>.
