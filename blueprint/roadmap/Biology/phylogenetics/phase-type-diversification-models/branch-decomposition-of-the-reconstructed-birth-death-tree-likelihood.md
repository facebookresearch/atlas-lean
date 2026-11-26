# Branch decomposition of the reconstructed birth–death tree likelihood

Consider a constant-rate birth–death process with speciation rate $\lambda>0$ and extinction rate $\mu\ge 0$, $\lambda\ne\mu$, and let

$$E(z)=\frac{\mu-\mu e^{(\mu-\lambda)z}}{\lambda-\mu e^{(\mu-\lambda)z}}$$

be the probability (Kendall) that a lineage born at time $0$ has no descendants at time $z$. Let $T^*$ be the reconstructed tree of age $t$ with $\ell$ tips, internal branches $i=1,\dots,k$ of lengths $b_i$ ending at elapsed time $x_i$ before the present, and pendant branches of lengths $\tilde b_j$.

**Theorem.** The likelihood of $T^*$ factorizes over branches as

$$\mathcal L(T^*\mid\lambda,\mu)=(\ell-1)!\prod_{i=1}^{k}G_{x_i,t}(b_i)\,\lambda\prod_{j=1}^{\ell}D_t^{(1)}(\tilde b_j),$$

where $G_{x,t}$ and $D_t^{(1)}$ solve the linear equations

$$\frac{dG_{x,t}(z)}{dz}=-(\lambda+\mu)G_{x,t}(z)+2\lambda G_{x,t}(z)E(z+x),\qquad \frac{dD_t^{(1)}(z)}{dz}=-(\lambda+\mu)D_t^{(1)}(z)+2\lambda E(z)D_t^{(1)}(z),$$

with value $1$ at $z=0$, namely

$$G_{x,t}(z)=\Bigl(\frac{\lambda-\mu e^{(\mu-\lambda)x}}{\lambda-\mu e^{(\mu-\lambda)(z+x)}}\Bigr)^2e^{(\mu-\lambda)z},\qquad D_t^{(1)}(z)=\Bigl(\frac{(\lambda-\mu)e^{\mu z}}{\lambda-\mu e^{(\mu-\lambda)z}}\Bigr)^2e^{-(\lambda+\mu)z}.$$

$G_{x,t}(b)$ is the probability that a reconstructed internal branch persists for length $b$ with all hidden side branches going extinct before the present, and $D_t^{(1)}(\tilde b)$ the corresponding probability for a pendant branch that survives to the present. Conditioning on survival of both root lineages recovers the classical reconstructed-tree likelihood of Nee et al. (1994): $\mathcal L_{\mathrm{Nee}}=\mathcal L/(1-E(x_2))^2$ in the four-tip example of the paper.

## Expansion

Along a reconstructed branch, events occur at total rate $\lambda+\mu$; a death ends the lineage, and a birth whose one daughter leaves no descendants by the present ("hidden speciation") is invisible. Each birth offers two daughters that may be the hidden one, which gives the renewal equation $G(z)=e^{-(\lambda+\mu)z}+\int_0^z e^{-(\lambda+\mu)(z-u)}\,2\lambda\,G(u)E(u+x)\,du$ and its differential form; the same argument gives $D^{(1)}$. Both are first-order linear ODEs and integrate in closed form using $E$. The observed split at the end of an internal branch contributes the factor $\lambda$.

## Sources

- A. C. Soewongsono, B. R. Holland, M. M. O'Reilly, "The shape of phylogenies under phase-type distributed times to speciation and extinction", Bulletin of Mathematical Biology 84(10) (2022) 118, <https://doi.org/10.1007/s11538-022-01072-w>, PMCID PMC9474389. Section 2.4, Eqs. (19)–(26) and (27), with derivations in Appendices 6.4–6.5.
