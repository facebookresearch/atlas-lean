# Phase-locked states of a Kuramoto network with adaptive conduction delays

Consider the delayed Kuramoto network of the [non-plastic model](global-frequency-and-linear-stability-of-the-delayed-kuramoto-network.md), with no self-coupling ($a_{ii} = 0$ for every $i$), but with time-dependent delays $\tau_{ij}(t) \ge 0$ obeying the phase-dependent plasticity rule (time scale set to one)

$$\frac{d\tau_{ij}}{dt} = H(\tau_{ij})\bigl[-(\tau_{ij} - \tau^0_{ij}) + \kappa\,\sin(\theta_j - \theta_i)\bigr], \qquad \tau_{ij}(0) = \tau^0_{ij} \ge 0,$$

where $\kappa > 0$ is the plasticity gain and $H$ is a smooth cutoff with $H(\tau) = 0$ for $\tau < 0$ and $H(\tau) = 1$ for $\tau > \varepsilon$, which keeps delays nonnegative. The global frequency $\Omega$ and offsets $\Delta_{ij} = \phi_j - \phi_i$ of a synchronized state $\theta_i(t) \to \Omega t + \phi_i$ as $t\to\infty$, with delays converging to equilibrium values $\tau_{ij}(t)\to\tau^E_{ij}$, satisfy, for all $i, j$ (the source derives these equations by applying its phase-locked ansatz to the state reached as $t\to\infty$; it does not claim that they characterize existence, and since $\tau_{ij}(0)=\tau^0_{ij}$ the delays are not constant from $t=0$),

$$\Omega = \omega_0 + \frac{g}{N}\sum_{j=1}^N a_{ij}\sin(-\Omega\tau^E_{ij} + \Delta_{ij}), \qquad \tau^E_{ij} = \max\bigl(\tau^0_{ij} + \kappa\sin\Delta_{ij},\,0\bigr),$$

and again $\Omega \in [\omega_0 - g, \omega_0 + g]$. Put $C^0_{ij} = \cos\Delta_{ij}$, $C_{ij} = \cos(-\Omega\tau^E_{ij} + \Delta_{ij})$ and $H_{ij} = H(\tau^E_{ij})$. Linearizing with $\theta_i = \Omega t + \phi_i + \epsilon_i$ and $\tau_{ij} = \tau^E_{ij} + \eta_{ij}$, the modes $\epsilon_i = v_i e^{\lambda t}$, $\eta_{ij} = w_{ij}e^{\lambda t}$ ($\lambda \ne -1$) satisfy $w_{ij} = \kappa C^0_{ij}H_{ij}(v_j - v_i)/(\lambda + 1)$ and $M_\lambda v = 0$ with

$$(M_\lambda)_{ii} = \lambda(\lambda+1) + \frac{g}{N}\sum_j a_{ij}C_{ij}\bigl(\lambda + 1 - \Omega\kappa C^0_{ij}H_{ij}\bigr),$$

$$(M_\lambda)_{ij} = \frac{g}{N}\,a_{ij}C_{ij}\bigl[\Omega\kappa C^0_{ij}H_{ij} - (\lambda+1)e^{-\lambda\tau^E_{ij}}\bigr] \quad (i \ne j).$$

The state is linearly stable when every non-neutral root of $\det M_\lambda = 0$ has negative real part. For $\kappa = 0$ the delays stay at $\tau^0_{ij}$, the offsets vanish, and the criterion reduces to the non-plastic one. The source's Eq. (1) does not exclude $a_{ii} = 1$ (its two-oscillator section sets $a_{11} = a_{22} = 0$ "to remove all self-integration terms"), and its Eq. (14) gives the diagonal entry exactly as displayed above, dropping the $j = i$ term $\frac{g}{N}a_{ii}C_{ii}\bigl[\Omega\kappa C^0_{ii}H_{ii} - (\lambda+1)e^{-\lambda\tau^E_{ii}}\bigr]$ that Eq. (13) produces when $a_{ii} = 1$; with no self-coupling, as assumed here, Eq. (14) holds as printed.

## Depends on

- [Global frequency and linear stability of the delayed Kuramoto network](global-frequency-and-linear-stability-of-the-delayed-kuramoto-network.md)

## Expansion

At equilibrium the plasticity rule forces $\tau_{ij} = \tau^0_{ij} + \kappa\sin\Delta_{ij}$ wherever this is positive, so plastic delays can be maintained only with nonzero phase offsets: the network locks to a common frequency but not in phase. Delay perturbations around positive equilibrium delays obey $\dot\eta_{ij} = -\eta_{ij} + \kappa C^0_{ij}(\epsilon_j - \epsilon_i)$ and vanish asymptotically at zero equilibrium delays. Eliminating $w_{ij}$ from the phase equation and multiplying by $\lambda + 1$ gives the quadratic-in-$\lambda$ diagonal entries. The paper uses this criterion, and its large-$N$ limit, to show that delay plasticity enlarges the parameter range in which synchrony is stable.

## Sources

- S. H. Park and J. Lefebvre, "Synchronization and resilience in the Kuramoto white matter network model with adaptive state-dependent delays", Journal of Mathematical Neuroscience 10 (2020) 16, <https://doi.org/10.1186/s13408-020-00091-y>, PMCID PMC7494726. Section "Synchronized state and stability with plastic delays", Eqs. (1)–(14).
