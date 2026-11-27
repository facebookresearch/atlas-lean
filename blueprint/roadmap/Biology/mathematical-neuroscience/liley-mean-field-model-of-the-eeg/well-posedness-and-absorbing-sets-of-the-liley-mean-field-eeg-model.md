# Well-posedness and absorbing sets of the Liley mean field EEG model

**Model.** The Liley et al. mean field model of the neocortex describes, on a periodic spatial domain $\Omega$, mean soma membrane potentials $v = (h_e, h_i)$ of excitatory and inhibitory populations, synaptic activities $i$ (four components, $ee, ei, ie, ii$) and long-range cortico-cortical pulse densities $w$:

$$\Phi\,\partial_t v + v - J_1 i + J_2 v\, i^{\mathsf T}\Psi J_4 + J_3 v\, i^{\mathsf T}\Psi J_5 = 0,$$

$$\partial_t^2 i + 2\Gamma\partial_t i + \Gamma^2 i - e\Upsilon\Gamma J_6 w - e\Upsilon\Gamma N J_7 f(v) = e\Upsilon\Gamma g,$$

$$\partial_t^2 w + 2\nu\Lambda\partial_t w - \tfrac32\nu^2\Delta w + \nu^2\Lambda^2 w - \nu^2\Lambda^2 M J_8 f(v) = 0,$$

where $f$ is the sigmoidal firing-rate function, $g$ the subcortical input, the $J_k$ are constant selection matrices, and the remaining symbols are diagonal matrices of positive biophysical constants (membrane time constants, synaptic rate constants, conduction speed $\nu$, axonal decay $\Lambda$). The first equation is an ODE with bilinear (reversal-potential) coupling, the second a damped linear oscillator, and the third a damped telegraph-type wave equation.

**Theorem.**
1. *(Weak solutions.)* For $g \in L^2(0, T; L^2)$ and initial data $v_0, i_0, i_0' \in L^2$, $w_0 \in H^1$, $w_0' \in L^2$, there is a unique $\Omega$-periodic weak solution, depending continuously on the data, so the weak solution operators form a continuous semigroup.
2. *(Strong solutions.)* If moreover $w_0 \in H^2$ and $w_0' \in H^1$, the solution is a unique strong solution with the corresponding additional regularity.
3. *(Biophysical invariance.)* For bounded data in suitable phase spaces, $w$ stays nonnegative and the synaptic activities remain in a positively invariant region, as their interpretation requires.
4. *(Dissipativity.)* For bounded input $g$ the weak and strong semigroups possess bounded absorbing sets, under explicit inequalities on the parameters that hold over the whole biophysical range.
5. *(No compact global attractor in general.)* For time-independent bounded $g$, there are parameter values for which the set of equilibria is noncompact, so the semidynamical system lacks asymptotic compactness and has no compact global attractor.

## Expansion

Galerkin approximation in Fourier modes on the periodic domain with energy estimates gives existence; the bilinear terms $v\, i^{\mathsf T}$ are controlled because $v$ obeys a pointwise linear ODE in which $i$ enters multiplicatively, giving Grönwall-type bounds. Absorbing sets come from the damping in each subsystem and the boundedness of the sigmoid $f$. Asymptotic compactness fails because the $v$-equation has no spatial smoothing: equilibria can be spatially rough, and a noncompact continuum of equilibria rules out a compact attractor. This explains why simulations of the model can show highly complex, initial-condition-dependent behaviour.

## Sources

- Farshad Shirani, Wassim M. Haddad and Rafael de la Llave, "On the Global Dynamics of an Electroencephalographic Mean Field Model of the Neocortex", SIAM Journal on Applied Dynamical Systems 16 (2017), 1969–2029, <https://doi.org/10.1137/16m1098577>; numbering as in arXiv:1610.03140: Theorems 4.5, 4.7, 6.2, 6.3 and 7.5 and Propositions 5.1–5.6.
