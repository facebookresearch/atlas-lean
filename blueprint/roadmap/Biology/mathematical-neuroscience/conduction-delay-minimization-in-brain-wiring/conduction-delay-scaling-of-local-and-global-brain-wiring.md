# Conduction-delay scaling of local and global brain wiring

**Local circuits.** Model a local cortical circuit as $n$ neurons with all-to-all potential
synaptic connectivity, wired by nonmyelinated local wires (axons and dendrites) of diameter $d$. The
mean conduction delay is the mean path length $\ell$ between connected neurons divided by the
conduction velocity $s$, and cable theory gives a sublinear velocity–diameter law:

$$t = \frac{\ell}{s}, \qquad s = \beta d^{\theta}, \quad 0 < \theta < 1, \qquad\text{so}\qquad
t = \frac{\ell}{\beta d^{\theta}} .$$

Take $\ell$ to be of the order of the linear size of the network. As $d \to 0$ the volume tends to
the fixed nonwire (synaptic) volume and $t \sim d^{-\theta}$ diverges; for large $d$ the wiring
dominates, the linear size grows like $d$, and $t \sim d^{1-\theta}$. Hence $t$ has a minimum at an
optimal diameter at which nonwire occupies a fixed fraction of the volume. With $n^2$ potential
synapses of mean volume $v_s$, this gives the scaling relations (numerical factors dropped)

$$V \sim n^2 v_s, \qquad d \sim v_s^{1/3}, \qquad \ell \sim V^{1/3} \sim n^{2/3} v_s^{1/3},$$

and, for the cable-theory exponent $\theta = 1/2$, the smallest attainable mean delay

$$t_{\min} \sim \frac{n^{2/3} v_s^{1/6}}{\beta} .$$

**Global connections.** If each of $N$ neurons sends one myelinated global axon of diameter $D$ and
length $L$ to another local network, with linear velocity law $S = B D$, then

$$T = \frac{L}{B D}, \qquad L \sim V^{1/3}, \qquad V \sim N L D^2
\quad\Longrightarrow\quad L \sim N^{1/2} D, \qquad T \sim \frac{N^{1/2}}{B},$$

independent of the global axon diameter.

## Expansion

Because $t_{\min}$ grows like $n^{2/3}$, a tolerable delay bounds the size of an all-to-all
network. With $v_s$ a fraction of a cubic micrometre, $\beta \sim 1\ \mathrm{m\,s^{-1}\,\mu m^{-1/2}}$
and a delay budget of about a millisecond, $n_{\max} \sim 10^4$ neurons, the size of a cortical
column; all-to-all wiring of the $10^{10}$ neurons of human neocortex would cost delays of seconds.
Sparse global wiring escapes this: $T \sim N^{1/2}/B$ with $B \sim 5\ \mathrm{m\,s^{-1}\,\mu m^{-1}}$
gives about $20$ ms for $N \sim 10^{10}$ and about $0.6$ ms for mouse neocortex ($N \sim 10^7$),
because thicker myelinated axons speed conduction exactly as fast as they inflate the brain. The two
requirements then compete: global axons running through gray matter lengthen local wires, which
raises local delay in proportion to the volume fraction they occupy, and segregating them into
white-matter tracts, at the cost of a gray–white boundary effect, is what keeps both delays short.
All estimates are order-of-magnitude scaling laws.

## Sources

- Q. Wen, D. B. Chklovskii, "Segregation of the brain into gray and white matter: a design
  minimizing conduction delays", PLoS Computational Biology 1 (2005) e78, Results, Eqs. (1)-(6)
  (local circuits) and Eqs. (7)-(13) (global connections),
  <https://doi.org/10.1371/journal.pcbi.0010078> (PMC1323466).
