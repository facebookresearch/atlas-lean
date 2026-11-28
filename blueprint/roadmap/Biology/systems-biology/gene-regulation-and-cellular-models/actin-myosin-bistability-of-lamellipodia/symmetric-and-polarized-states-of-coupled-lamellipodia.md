# Symmetric and polarized steady states of two coupled lamellipodia

Model a lamellipodial cell fragment as two back-to-back planar lamellipodia with filament angles $\omega, \hat\omega$ and positions $y, \hat y$. They are coupled through a constant membrane force $f_{mem}$ and a size-dependent stress-fibre force $f_{stress}(y + \hat y)$:

$$
\mu_A (\dot y + \dot{\hat y}) = -\frac{2}{L}\big(f_{mem} + f_{stress}(y + \hat y)\big) + \mu_A v (\sin\omega + \sin\hat\omega),
$$

$$
\dot\omega\, g(\omega) = \cos\omega \left(\frac{f_{stress}(y+\hat y) - f_{mem}}{4} + h(\omega)\right),
\qquad
\dot{\hat\omega}\, g(\hat\omega) = \cos\hat\omega \left(\frac{f_{stress}(y+\hat y) - f_{mem}}{4} + h(\hat\omega)\right).
$$

Here $g > 0$ and $h$ is the cross-link/myosin twisting function of the single lamellipodium.

**Theorem 3.** Assume the stiffness-ratio condition of Lemma 1, so that $h$ has stable zeros $\omega_{10} > \omega_{30}$. Let $f_{stress}$ be $C^1$ with bounded positive derivative, and let $f_{mem}$, $\mu_A v L$ and the Lipschitz constant of $f_{stress}$ be small enough. Then the system has four stable steady states:

$$
(\omega, \hat\omega) \in \{(\omega_{CL}, \omega_{CL}),\ (\omega_{MY}, \omega_{MY}),\ (\omega_{CL}, \omega_{MY}),\ (\omega_{MY}, \omega_{CL})\},
$$

with $\omega_{CL} = \omega_{10} + O(f_{mem} + \mu_A v L)$ and $\omega_{MY} = \omega_{30} + O(f_{mem} + \mu_A v L)$. The fragment velocity is $\dot y = -\dot{\hat y} = \tfrac{v}{2}(\sin\omega - \sin\hat\omega)$. The two symmetric states are stationary. The two asymmetric states are polarized and migrate, with a cross-link-dominated front and a myosin-collapsed rear.

## Depends on

- [Filament-angle bistability of a planar lamellipodium](filament-angle-bistability-of-a-planar-lamellipodium.md)

## Expansion

At a steady state, $f_{stress}(y+\hat y) = -f_{mem} + \tfrac{\mu_A L v}{2}(\sin\omega + \sin\hat\omega)$, so $h(\omega)$ and $h(\hat\omega)$ are $O(f_{mem} + \mu_A v L)$. A perturbation argument then puts each angle near a simple zero of $h$. The Jacobian has a weak coupling $\kappa = f_{stress}' \ll 1$. Its eigenvalues are $A h'(\omega) + O(\kappa)$, $\hat A h'(\hat\omega) + O(\kappa)$, and $\kappa\big(-\tfrac{2}{\mu_A L} + v\cos\omega / h'(\omega) + v\cos\hat\omega / h'(\hat\omega)\big) + O(\kappa^2)$. All three are negative at the four combinations of stable zeros. This gives a mechanical explanation for the coexistence of stationary circular fragments and moving crescent-shaped fragments observed in keratocytes. An analogous result holds with constant stress-fibre force and size-dependent membrane force.

## Sources

- Hirsch S, Manhart A, Schmeiser C. Mathematical modeling of myosin induced bistability of lamellipodial fragments. *Journal of Mathematical Biology* 74 (2017) 1–22. <https://doi.org/10.1007/s00285-016-1008-2>. PMCID: PMC5206284.
