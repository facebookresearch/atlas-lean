# Observed Data congr

Let $\Omega$ be a set, $R \subseteq \Omega$ the event of the respondents, $X : \Omega \to \mathcal X$ an always-observed covariate and $Y : \Omega \to \mathcal Y$ an outcome, recorded only on $R$. Let $Y' : \Omega \to \mathcal Y$ be a second outcome with $Y(\omega) = Y'(\omega)$ for every $\omega \in R$. Then the observed-data maps of $(R, X, Y)$ and $(R, X, Y')$ coincide, where the observed-data map is

$$O(\omega) = \begin{cases} (X(\omega), Y(\omega)) & \omega \in R, \\ (X(\omega), \ast) & \omega \notin R, \end{cases}$$

with $\ast$ a missing marker. Thus the observed data do not depend on the outcome of nonrespondents.
