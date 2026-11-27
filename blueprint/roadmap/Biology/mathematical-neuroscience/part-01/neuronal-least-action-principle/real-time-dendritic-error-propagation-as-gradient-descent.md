# Real-time dendritic error propagation as gradient descent

**Setting.** A network $W$ (arbitrary, possibly recurrent) runs the least-action voltage and error dynamics $\tau\dot u = -u + Wr + e$, $\bar e = \bar r'_{\mathrm{net}}\odot W^{\mathsf T}_{\mathrm{net}}\bar e + \beta\bar e^*$, with Lagrangian $L = E^M + \beta C$, mismatch energy $E^M = \tfrac12\|u - W\bar r\|^2$ and output cost $C = \tfrac12\|u^*_o - u_o\|^2$. Synapses follow the local rule ("postsynaptic dendritic error times low-pass filtered presynaptic rate")

$$\dot W = \eta\,(u - W\bar r)\,\bar r^{\mathsf T} = \eta\,\bar e\,\bar r^{\mathsf T}.$$

**Theorem (rt-DeEP).** Along the voltage trajectories, at every moment long enough after initialization,
1. for any $\beta \ge 0$, $\bar e\,\bar r^{\mathsf T} = -\dfrac{dL}{dW}$, and $\lim_{\beta\to\infty}\bar e\,\bar r^{\mathsf T} = -\dfrac{dE^M}{dW}$;
2. for weak nudging, $\lim_{\beta\to0}\dfrac1\beta\,\bar e\,\bar r^{\mathsf T} = -\dfrac{dC}{dW}$,
where $dL/dW$, $dC/dW$ are total derivatives through the instantaneous network map $u_o = F_W(\bar r_{\mathrm{in}})$. The statements hold even when the input rates contain delta functions and the targets contain steps.

## Depends on

- [Euler–Lagrange dynamics of the neuronal least-action principle](euler-lagrange-dynamics-of-the-neuronal-least-action-principle.md)

## Expansion

On the trajectory the voltages satisfy $\partial L/\partial u = 0$, so by the envelope argument the total derivative of $L$ with respect to $W$ equals the partial derivative, $dL/dW = \partial L/\partial W = -\bar e\,\bar r^{\mathsf T}$. For small $\beta$, $C = \partial L/\partial\beta$ and exchanging the derivatives in $\beta$ and $W$ gives part 2, the equilibrium-propagation limit, now valid in real time because the prospective dynamics keep the network in a moving equilibrium rather than requiring relaxation to a fixed point for each static input. For large $\beta$ outputs are clamped to targets and learning drives every neuron's mismatch to zero; if all mismatches vanish the output cost vanishes too. Thus a rule local in space and time performs gradient descent on a global, time-dependent cost.

## Sources

- W. Senn, D. Dold, A. F. Kungl, B. Ellenberger, J. Jordan, Y. Bengio, J. Sacramento, M. A. Petrovici, "A neuronal least-action principle for real-time learning in cortical circuits", eLife 12 (2024) RP89674, Results (local plasticity at basal synapses), Eq (8), Theorem 1, and Methods (proving Theorem 1), <https://doi.org/10.7554/eLife.89674>, PMCID PMC11661794.
