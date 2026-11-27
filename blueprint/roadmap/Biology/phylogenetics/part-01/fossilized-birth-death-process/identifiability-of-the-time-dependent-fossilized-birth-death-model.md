# Identifiability of the time-dependent fossilized birth–death model

**Process.** Time runs backwards from the origin $t_0 > 0$ to the present $0$. Starting from one
lineage, lineages independently speciate, go extinct and are sampled (fossils) at time-dependent
rates $\lambda(t), \mu(t), \psi(t) \ge 0$, Lebesgue-integrable on $[0, t_0]$; sampled lineages stay
in the process (sampled ancestors are possible), and extant lineages are sampled at the present with
probability $\rho_0$.

**Complete trees.** A complete tree with $N_0$ present-day taxa, branching times $x_i$, death times
$y_j$ and sampling times $z_k$ has density

$$f_{\mathrm{compl}}(T) = \Psi(t_0) \prod_{i=1}^{N_0 + n - 1} \lambda(x_i)\Psi(x_i)
 \prod_{j=1}^{n} \frac{\mu(y_j)}{\Psi(y_j)} \prod_{k=1}^{m} \psi(z_k),
\qquad \Psi(t) = e^{-\int_0^t (\lambda + \mu + \psi)(u)\, du}.$$

**Reconstructed trees.** Let $E(t)$ be the probability that a lineage alive at time $t$ leaves no
sampled descendant:

$$\frac{dE}{dt} = -(\lambda + \mu + \psi) E + \lambda E^2 + \mu, \qquad E(0) = 1 - \rho_0 ,$$

which has a unique extended solution on $[0, t_0]$ if $\int_0^t \lambda(s) e^{-\int_0^s (\lambda - \mu -
\psi)(u)\,du}\, ds < \infty$ and either $\rho_0 > 0$ or $\psi(0) > 0$ with the rates continuous at $0$.
The density of reconstructed trees (observed lineages only) conditioned on at least one sample is
$f_{\mathrm{rec}}(T)/(1 - E(t_0))$, with $f_{\mathrm{rec}}$ built from
$\Phi(t) = e^{\int_0^t (2\lambda E - \lambda - \mu - \psi)(u)\, du}$.

**Theorem (complete trees).** For fixed $t_0$, the map $(\lambda, \mu, \psi) \mapsto f_{\mathrm{compl}}$ is
injective up to almost-everywhere equality of the rate functions: the time-dependent FBD complete tree
model is identifiable.

**Theorem (reconstructed trees).** For fixed $t_0$, if the conditions above hold and $\psi(t) > 0$ for
almost all $t$, the time-dependent FBD reconstructed tree model with parameters
$(\lambda, \mu, \psi, \rho_0)$ is identifiable.

## Expansion

For complete trees, equality of densities forces equality of the per-event factors almost
everywhere, in particular $\lambda_1 \Psi_1 = \lambda_2 \Psi_2$, and the analogous identities for
deaths and samples; comparing these pins down each rate. For reconstructed trees, the key device is
the **pulled rates**

$$\tilde\lambda = \lambda (1 - E), \qquad \tilde\mu = \frac{\psi E}{1 - E}, \qquad \tilde\psi = \psi,
\qquad \tilde\rho_0 = 1,$$

a one-to-one transformation when $\psi > 0$ (which makes $E < 1$ on $(0, t_0]$). The conditioned
density of reconstructed trees under the original rates equals the density of complete trees under the
pulled rates, so equal reconstructed-tree distributions give equal pulled rates by the
complete-tree theorem and hence equal original rates. This contrasts with the birth–death and
birth–death-sampling models in which sampling removes lineages: there, whole congruence classes of
rate functions give the same reconstructed-tree distribution. Sampled ancestors carry the
information that breaks the congruence.

## Sources

- K. Truman, T. G. Vaughan, A. Gavryushkin, A. S. Gavryushkina, "The Fossilized Birth-Death Model Is
  Identifiable", Systematic Biology 74 (2025) 112-123, Eqs. (1)-(4) and (10), Proposition 1,
  Definition 1, Theorems 2 and 4, Lemmas 3, 5 and 6, <https://doi.org/10.1093/sysbio/syae058>
  (PMC11997801).
