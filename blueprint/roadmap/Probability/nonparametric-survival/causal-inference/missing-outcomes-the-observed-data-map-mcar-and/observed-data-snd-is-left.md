# Observed Data snd is Left

Let $\Omega$ be a set, $R \subseteq \Omega$ the event of the respondents, $X : \Omega \to \mathcal X$ an always-observed covariate and $Y : \Omega \to \mathcal Y$ an outcome, recorded only on $R$. Let $O$ be the observed-data map,

$$O(\omega) = \begin{cases} (X(\omega), Y(\omega)) & \omega \in R, \\ (X(\omega), \ast) & \omega \notin R, \end{cases}$$

with $\ast$ a missing marker outside $\mathcal Y$. Then the observed data reveal the response indicator: for every $\omega \in \Omega$, the second coordinate of $O(\omega)$ lies in $\mathcal Y$ (rather than being $\ast$) if and only if $\omega \in R$.
