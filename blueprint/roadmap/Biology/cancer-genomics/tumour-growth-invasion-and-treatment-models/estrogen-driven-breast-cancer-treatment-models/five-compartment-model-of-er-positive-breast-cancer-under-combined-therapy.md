# Five-compartment model of ER-positive breast cancer under combined therapy

**Model.** Normal cells $N$, tumor cells $T$, immune cells $I$, estrogen $E$ and an immunotherapy agent $M$ evolve by

$$\dot N=N(a_1-b_1N)-\frac{d_1TN}{1+\epsilon T}-l_1NE(1-k),$$

$$\dot T=T(a_2d-b_2T)-g_1IT-m_dT+l_1NE(1-k),$$

$$\dot I=s+\frac{rIT}{o+T}-g_2IT-mI-\frac{l_3IE}{g+E}(1-k)+\frac{p_MIM}{j_M+M},$$

$$\dot E=p(1-k)-\theta E,\qquad \dot M=v_M(t)-n_MM+\frac{\chi MI}{\xi+I}.$$

Here $k\in[0,1]$ is the efficacy of endocrine therapy (blocking estrogen production and action), $d$ is the ketogenic-diet dose modulating tumor growth, $m_d$ is the tumor death rate due to nutrient starvation, $l_1NE$ is estrogen-induced transformation of normal cells (DNA damage), $d_1TN/(1+\epsilon T)$ is saturated tumor damage to normal tissue, $s$ is the immune source, the Michaelis–Menten terms describe tumor-stimulated immune recruitment and immunotherapy activation, and $v_M$ is the immunotherapy dosing schedule.

**Results.**
1. The system has a unique solution, and $\mathbb R^5_+$ is positively invariant.
2. Estrogen relaxes to $E^*=p(1-k)/\theta$ exponentially at rate $\theta$, so endocrine therapy scales the estrogen load, and hence the transformation flux $l_1NE^*(1-k)=l_1p(1-k)^2N/\theta$, quadratically in $1-k$.

## Expansion

The estrogen and immunotherapy equations decouple from the cell populations except through $I$, so the long-time estrogen level is set by production and clearance alone, and endocrine therapy acts twice: on estrogen production and on its effect. With $k<1$ the transformation term keeps feeding the tumor compartment: at $E=E^*>0$, any equilibrium with $T=0$ must have $N=0$, so the system has no tumor-free equilibrium with healthy tissue unless endocrine therapy is fully effective ($k=1$). (The source's stability analysis linearizes at a point with $T=0$ and $N>0$, which for $k<1$ is not an equilibrium of its system, so its stability theorems are not stated here.) Numerical simulations in the source compare treatment combinations of diet (reducing tumor growth) and immunotherapy (raising immune killing).

## Sources

- Hassnaa Akil and Nadia Idrissi Fatmi, "A mathematical model of Breast cancer (ER+) with excess estrogen: Mixed treatments using Ketogenic diet, endocrine therapy and Immunotherapy", arXiv:2205.11974 (2022), Section 2 (model), Theorems 1–2 (well-posedness and invariance), <https://doi.org/10.48550/arXiv.2205.11974>.
