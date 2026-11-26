# Global stability of Michaelis-Menten interaction networks

**Setting.** For $n\ge2$ species with concentrations $x_i\ge0$, consider

$$\dot x_i=-d_ix_i+f_i(x),\qquad f_i(x)=b_i+\sum_{j\ne i}h_{ij}(x_j),\qquad i=1,\dots,n,$$

with decay rates $d_i>0$, constant inputs $b_i\ge0$, and each interaction $h_{ij}$ either identically zero or of Michaelis-Menten form, activating $h_{ij}(s)=a_{ij}\,s/(k_{ij}+s)$ or inhibiting $h_{ij}(s)=a_{ij}\,k_{ij}/(k_{ij}+s)$, with $a_{ij},k_{ij}>0$. Draw an edge $j\to i$ when $h_{ij}\not\equiv0$. The hypotheses are: (A1) *no idle node*, each $i$ has $b_i>0$ or an incoming edge; (A2) the graph is strongly connected (which implies (A1)); (A3) *non-degeneracy*, some interaction is inhibitory or some $b_i>0$. On $(0,\infty)^n$ use Thompson's logarithmic metric $\rho(x,z)=\max_i|\log x_i-\log z_i|$.

**Lemma 1 (logarithmic contraction).** Each Michaelis-Menten function satisfies $s|h'(s)|/h(s)=1-h(s)/a\in(0,1)$ for $s>0$; hence $|\log h(s)-\log h(\sigma)|<|\log s-\log\sigma|$ for $s\ne\sigma$. Under (A1), $|\log(f_i(x)/f_i(z))|<\rho(x,z)$ for all positive $x\ne z$ (Corollary 1).

**Theorem 2 (trajectories attract each other).** Under (A1), for any two positive solutions $x(t)\ne z(t)$, the distance $\rho(x(t),z(t))$ is strictly decreasing on $[0,\infty)$.

**Theorem 3 (global stability on the open orthant).** Under (A1), if a positive equilibrium $\bar x$ exists then it is the only positive equilibrium, $V(x)=\max_i|\log(x_i/\bar x_i)|$ is a strict Lyapunov function, and every positive solution converges to $\bar x$.

**Theorem 4 (global stability on the closed orthant).** Under (A2) and (A3), the system has exactly one equilibrium in $[0,\infty)^n$; it is strictly positive and globally asymptotically stable on $[0,\infty)^n$. If (A3) fails (all $b_i=0$ and all interactions activating), then either $0$ is globally asymptotically stable or there is a unique positive equilibrium attracting all of $(0,\infty)^n$ (Theorem 5).

**Theorem 6 (delays).** Under (A2) and (A3), replacing $h_{ij}(x_j(t))$ by $h_{ij}(x_j(t-\tau_{ij}))$ with arbitrary constant delays $\tau_{ij}\ge0$ preserves global asymptotic stability of the same equilibrium for all nonnegative continuous initial data.

## Expansion

The identity in Lemma 1 says every Michaelis-Menten response has logarithmic gain strictly below one, whether activating or inhibiting; a sum of such terms plus a nonnegative constant inherits strict contraction in the log metric. In log coordinates $u_i=\log x_i$ the equation reads $\dot u_i=d_i(e^{\log f_i-u_i}-1)$, and at a coordinate $i$ realizing the maximum of $|u_i-w_i|$ the contraction makes the difference decrease, so the sup-norm distance between two solutions strictly decreases. Taking $z(t)\equiv\bar x$ gives the Lyapunov function; boundedness (solutions enter the box $x_i\le c_i$) and Brouwer's theorem give existence of an equilibrium, and strong connectedness with non-degeneracy excludes boundary equilibria. At the equilibrium, $D^{-1}JD$ with $D=\mathrm{diag}(\bar x)$ is strictly row-diagonally dominant with negative diagonal, which gives local exponential stability (Theorem 1). This settles the global stability question left open for these networks.

## Sources

- E. D. Sontag, "Global stability of Michaelis-Menten networks", arXiv preprint (2026), Lemma 1, Corollary 1, Theorems 1-6, <https://doi.org/10.48550/arXiv.2610.24351>.
