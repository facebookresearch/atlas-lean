# Spike-sequence controllability of integrate-and-fire neurons under common optogenetic input

**Model.** An uncoupled ensemble of leaky integrate-and-fire neurons is driven by one common,
nonnegative light-gated conductance $g_C(t) \ge 0$:

$$\frac{dv_k}{dt} = -\alpha_k v_k + g_C(t)\, \beta_k (E - v_k), \qquad k = 1, \dots, N,$$

where $\alpha_k > 0$ is the leak rate, $\beta_k > 0$ the neuron's sensitivity to the light, and the
channel reversal potential $E$ exceeds the spike threshold $v_T$; when $v_k$ reaches $v_T$ the neuron
spikes and resets to $0$.

**Controllability notions.** A spike sequence is a list of neuron labels $(s_1, \dots, s_M)$ in firing
order, without timing; a spike pattern adds the firing times. The ensemble is sequence (pattern)
controllable if every sequence (pattern) can be produced by some admissible input from any initial
condition.

**Proposition (necessary condition).** For a heterogeneous pair labelled so that $\alpha_1 > \alpha_2$,
sequence controllability requires

$$\frac{\alpha_1 - \alpha_2}{\beta_1 - \beta_2} > 0, \qquad\text{that is,}\qquad \beta_1 > \beta_2 .$$

**Proposition (sufficient condition).** The pair is sequence controllable if, in addition,

$$\frac{\alpha_1}{\beta_1} > \frac{\alpha_2}{\beta_2}.$$

**Synchronizing conductance.** If the two neurons share a voltage $v_1 = v_2 = v^* \in (0, E)$, the
conductance

$$g^* = \frac{\alpha_2 - \alpha_1}{\beta_2 - \beta_1}\cdot\frac{v^*}{E - v^*}$$

makes the voltage difference $v_2 - v_1$ stationary at that voltage, and $g^* > 0$ by the necessary
condition ($\alpha_1 > \alpha_2$ and $\beta_1 > \beta_2$). At $g_C = g^*$ the common voltage changes at
rate $v^*(\alpha_1\beta_2 - \alpha_2\beta_1)/(\beta_1 - \beta_2)$, so it rises exactly when the
sufficient condition holds; then applying $g_C(t) = g^*(v(t))$ along the common trajectory keeps
$v_1 = v_2$ and carries both neurons together to threshold. At $v^* = 0$ the formula gives $g^* = 0$
and the origin is an equilibrium, so a pair at rest needs a pre-pulse to leave it.

## Expansion

For the necessary condition: if $\beta_1 < \beta_2$ while $\alpha_1 > \alpha_2$, then at any common
voltage $v^*$ one has $\dot v_1 < \dot v_2$ for every $g_C \ge 0$, so neuron 1 can never overtake
neuron 2 from below, and no sequence in which neuron 1 fires twice without neuron 2 firing in between
is reachable. For a randomly drawn pair from a generic heterogeneous ensemble this fails with
probability about one half, so common input severely limits control. For sufficiency, rescale time
by $\alpha_1$ and the input by $\beta_1/\alpha_1$; for each constant input $g$ the subthreshold
dynamics has the stable equilibrium $\bigl(gE/(1 + g),\ gE/(\hat\alpha/\hat\beta + g)\bigr)$ with
$\hat\alpha = \alpha_2/\alpha_1$, $\hat\beta = \beta_2/\beta_1$, and the second condition
($\hat\alpha < \hat\beta$) puts this curve above the diagonal. An intermediate input then makes only
neuron 2 cross threshold, while a large input applied from rest makes neuron 1 cross first, owing to
its faster relaxation, so pulses of two amplitudes realize any order. Pairwise conditions extend to
large ensembles: a common input can select which subensemble fires, with heterogeneity of
$(\alpha_k, \beta_k)$ acting as the resource that underactuated control exploits.

## Sources

- S. Ching, J. T. Ritt, "Control strategies for underactuated neural ensembles driven by optogenetic
  stimulation", Frontiers in Neural Circuits 7 (2013) 54, Definitions 1-3, Eq. (1), Propositions 1-2
  with Eqs. (2)-(7), <https://doi.org/10.3389/fncir.2013.00054> (PMC3620532).
