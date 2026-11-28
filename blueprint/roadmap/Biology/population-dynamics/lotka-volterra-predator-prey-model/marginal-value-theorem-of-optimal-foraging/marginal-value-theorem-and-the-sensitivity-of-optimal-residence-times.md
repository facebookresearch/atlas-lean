# Marginal value theorem and the sensitivity of optimal residence times

**Setting.** Patches of types $i = 1, \dots, s$ occur with frequencies $p_i > 0$ ($\sum_i p_i = 1$). Exploiting a type-$i$ patch for time $t$ yields cumulative net gain $F_i(x_i, t)$, positive, increasing and eventually concave in $t$, where $x_i$ is a patch attribute; reaching a type-$i$ patch takes travel time $T_i(x_i) > 0$. Write $\langle y_j \rangle = \sum_j p_j y_j$. With residence times $t = (t_1, \dots, t_s)$ the long-term rate of gain is

$$E_n(t) = \frac{\langle F_j(x_j, t_j) \rangle}{\langle T_j(x_j) + t_j \rangle}.$$

**Marginal value theorem.** At the optimum there is a set $\Omega$ of exploited patch types with

$$\frac{\partial F_i}{\partial t}(x_i, t_i^*) = E_n^* = \frac{\langle F_j(x_j, t_j^*) \rangle}{\langle T_j + t_j^* \rangle} \quad (i \in \Omega), \qquad t_i^* = 0 \quad (i \notin \Omega):$$

leave every exploited patch when its marginal gain rate equals the maximal average rate $E_n^*$. In a homogeneous habitat ($F_i = F$, $T_i = T$) this is $F'(t^*) = F(t^*)/(T + t^*)$, the tangent construction.

**Quality.** Call $x_i$ a *metric of quality* if $\partial E_n^* / \partial x_i > 0$. Then $x_i$ is a metric of quality iff

$$\frac{\partial \ln \langle F_j(x_j, t_j^*) \rangle}{\partial x_i} - \frac{\partial \ln \langle T_j(x_j) \rangle}{\partial x_i}\, \frac{\langle T_j \rangle}{\langle T_j + t_j^* \rangle} > 0,$$

so only absolute gains and travel times matter, not the slope of the gain function.

**Homogeneous habitat.** Assuming $\partial^2 F / \partial t^2 (x, t^*) < 0$, increasing $x$ increases $t^*$ iff

$$\frac{\partial}{\partial x} \ln \frac{\partial F}{\partial t}(x, t^*) - \frac{\partial \ln F(x, t^*)}{\partial x} + \frac{d \ln T(x)}{dx}\, \frac{T(x)}{T(x) + t^*} > 0,$$

i.e. iff the relative increase of the marginal gain rate at $t^*$ exceeds the relative increase of realized fitness $\partial \ln E_n^* / \partial x$. An improvement in quality lengthens residence only if it steepens the gain curve enough.

**Heterogeneous habitat.** For $k \in \Omega$, increasing $x_i$ increases $t_k^*$ iff $\frac{\partial}{\partial x_i} \ln \frac{\partial F_k}{\partial t}(x_k, t_k^*) - \frac{\partial \ln E_n^*}{\partial x_i} > 0$. Hence improving the quality of one patch type shortens the optimal residence time on every other exploited type, and, for given patch-level observables, $\partial t_i^* / \partial x_i$ is larger in a heterogeneous habitat than in a homogeneous one (the habitat dilutes the feedback through $E_n^*$).

**Travel time.** If travel times increase while gain functions are unchanged, $\partial_{x} \ln \partial_t F_k = 0$ and $E_n^*$ decreases, so all optimal residence times increase.

## Expansion

Since $E_n$ is maximized, $\partial E_n / \partial t_l = 0$ at the optimum for every $l \in \Omega$; this gives the marginal value condition and, by the envelope theorem, makes $\partial E_n^* / \partial x_i$ equal to the partial derivative at fixed $t^*$, which yields the quality criterion. Differentiating the identity $\partial_t F_k(x_k, t_k^*) = E_n^*$ with respect to $x_i$ gives

$$\frac{d t_k^*}{d x_i} = -\frac{E_n^*}{\partial_t^2 F_k(x_k, t_k^*)} \Bigl( \frac{\partial}{\partial x_i} \ln \partial_t F_k(x_k, t_k^*) - \frac{\partial \ln E_n^*}{\partial x_i} \Bigr),$$

and concavity at $t_k^*$ fixes the sign. For $k \ne i$ the first term vanishes, so the sign is that of $-\partial E_n^* / \partial x_i$. When patch quality multiplies the gain curve, $F_i = x_i G_i(t)$, residence time on an improved patch always increases in a heterogeneous habitat, while in a homogeneous habitat such vertical scaling leaves $t^*$ unchanged.

## Sources

- V. Calcagno, L. Mailleret, É. Wajnberg, F. Grognard, "How optimal foragers should respond to habitat changes: a reanalysis of the Marginal Value Theorem", Journal of Mathematical Biology (2014), "The Marginal Value Theorem" (Eqs. 1–5), Definition 1 and Proposition 1 (Eqs. 6–8), Theorem 1 (Eqs. 9–11), Theorem 2 and Corollary 1, Proposition 2, Theorem 3, and Applications (travel time, Eq. 19; vertical scaling, Eqs. 23–24). <https://doi.org/10.1007/s00285-013-0734-y> (PMC4194746).
