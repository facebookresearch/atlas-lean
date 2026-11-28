# Current-sum LFP proxy of an integrate-and-fire network

Consider $N = 5000$ leaky integrate-and-fire neurons, $80\%$ excitatory (pyramidal) and $20\%$ inhibitory (interneurons), with each directed pair connected independently with probability $0.2$. The membrane potential of neuron $k$ (resting potential $0$) obeys

$$\tau_m \frac{dV_k}{dt} \;=\; -V_k + I_{A,k}(t) - I_{G,k}(t),$$

where $I_{A,k} \ge 0$ and $I_{G,k} \ge 0$ are the magnitudes of the AMPA-type (excitatory) and GABA-type (inhibitory) synaptic currents, and $\tau_m = 20$ ms for pyramidal cells and $10$ ms for interneurons. When $V_k$ reaches $V_{\mathrm{thr}} = 18$ mV, the neuron spikes, is reset to $V_{\mathrm{res}} = 11$ mV, and is refractory for $2$ ms (pyramidal) or $1$ ms (interneuron). Each presynaptic spike at time $t^*$ adds to the current of the corresponding type a difference-of-exponentials pulse

$$J\,\frac{\tau_m}{\tau_d - \tau_r}\Bigl(e^{-(t - t^* - \tau_L)/\tau_d} - e^{-(t - t^* - \tau_L)/\tau_r}\Bigr)\,\mathbf 1\{t \ge t^* + \tau_L\},$$

with latency $\tau_L = 1$ ms, rise and decay times $\tau_r < \tau_d$ specific to AMPA or GABA, and efficacy $J$ depending on the pre- and postsynaptic populations; external input arrives as Poisson spike trains through AMPA synapses, with a common time-varying rate. The simulated LFP is the sum of the absolute synaptic currents onto pyramidal cells,

$$\mathrm{LFP}(t) \;=\; \sum_{k \in \text{pyramidal}} \bigl(|I_{A,k}(t)| + |I_{G,k}(t)|\bigr),$$

reflecting that pyramidal dendrites form an approximately open-field dipole, with excitatory currents entering apically and inhibitory currents leaving basally.

## Expansion

Each pulse is the impulse response of the linear cascade $\tau_r \dot x = -x + \tau_m J\sum\delta(t - t^* - \tau_L)$, $\tau_d \dot I = -I + x$, which is why the currents can be integrated with two auxiliary variables per synapse type; the normalization written here gives each pulse area $\tau_m J$. Strong recurrent inhibition puts the network in an inhibition-dominated regime: single neurons fire irregularly at low rates, while the population shows oscillations. Delayed interactions among interneurons favour high (gamma) frequencies, and excitatory–inhibitory loops favour lower ones, with frequency set by delays, synaptic time constants and the balance of excitation and inhibition. Driven by thalamic activity recorded during natural movies, the LFP proxy reproduced both the power spectrum and the frequency-resolved stimulus information of primary visual cortex LFPs, whereas the network-averaged membrane potential decayed too fast at high frequencies.

## Sources

- A. Mazzoni, S. Panzeri, N. K. Logothetis, N. Brunel, "Encoding of naturalistic stimuli by local field potential spectra in networks of excitatory and inhibitory neurons", *PLoS Computational Biology* 4(12) (2008) e1000239, Methods, network model (Equations 1–5, Tables 2–3) and "Generation of Simulated Local Field Potentials", <https://doi.org/10.1371/journal.pcbi.1000239> (PMC2585056).
