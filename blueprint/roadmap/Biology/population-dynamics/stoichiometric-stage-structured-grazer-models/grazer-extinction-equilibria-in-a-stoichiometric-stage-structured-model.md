# Grazer extinction equilibria in a stoichiometric stage-structured model

**Model.** Producer carbon $x$, juvenile grazers $J$ and adult grazers $A$, with total phosphorus $P$, minimal producer P:C quota $q$, producer quota $Q = (P - \theta_j J - \theta_a A)/x$ and grazer P:C requirements $\theta_j$ (for producing juvenile biomass) and $\theta_a$ (for maturation growth):

$$\begin{aligned}
\dot x &= b x\Bigl(1 - \frac{x}{K}\Bigr)\Bigl(1 - \frac{q}{Q}\Bigr) - f_j(x) J - f_a(x) A,\\
\dot J &= e_a h_j(Q) f_a(x) A - e_j h_a(Q) f_j(x) J - \delta_j J,\\
\dot A &= e_j h_a(Q) f_j(x) J - \delta_a A,
\end{aligned}$$

with Holling type II ingestion $f_i(x) = c_i x/(a_i + x)$, stoichiometric co-limitation $h_i(Q) = \tanh(Q/\theta_i)$, conversion efficiencies $e_i$ and death rates $\delta_i$.

**Theorem.**
1. The set $\Omega = \{0 \le x \le \min\{K, P/q\},\ J, A \ge 0,\ qx + \theta_j J + \theta_a A < P\}$ is positively invariant.
2. The grazer-free equilibrium $E_1 = (K, 0, 0)$ is locally asymptotically stable if $K < P/q$ and

$$e_j h_a(P/K) f_j(K)\bigl(e_a h_j(P/K) f_a(K) - \delta_a\bigr) < \delta_j \delta_a,$$

and unstable if $K > P/q$ or the reverse strict inequality holds.
3. The phosphorus-limited grazer-free equilibrium $E_2 = (P/q, 0, 0)$ is locally asymptotically stable if $K > P/q$ and

$$e_j h_a(q) f_j(P/q)\bigl(e_a h_j(q) f_a(P/q) - \delta_a\bigr) < \delta_j \delta_a,$$

and unstable if $K < P/q$ or the reverse strict inequality holds.

## Expansion

Positivity of the producer quota $Q$ and conservation of phosphorus give the invariant region: grazer biomass can never lock up more phosphorus than the system contains. At a grazer-free equilibrium the grazer subsystem decouples linearly into a $2 \times 2$ stage matrix (juveniles produced by adults, maturation of juveniles), and the stability condition is the requirement that the stage-structured net reproductive number $\frac{e_j h_a f_j}{e_j h_a f_j + \delta_j} \cdot \frac{e_a h_j f_a}{\delta_a}$ is below one, rearranged. Producer carbon is set by light (carrying capacity $K$) or by phosphorus ($P/q$), whichever binds, and stage-specific stoichiometric demands enter through the co-limitation factors evaluated at the corresponding producer quota.

## Sources

- T. Ascoli, D. P. Damay, J. Li, A. Peace, "Stoichiometric ontogenetic development influences population dynamics: Stage-structured model under nutrient co-limitations", arXiv:2511.13901 (2025), Theorems 3.1 and 3.2, <https://doi.org/10.48550/arXiv.2511.13901>.
