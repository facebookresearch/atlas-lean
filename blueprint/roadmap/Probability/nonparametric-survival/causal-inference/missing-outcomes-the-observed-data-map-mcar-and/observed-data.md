# Observed Data

Let $\Omega$ be a set, $R \subseteq \Omega$ the event of the respondents, $X : \Omega \to \mathcal X$ an always-observed covariate and $Y : \Omega \to \mathcal Y$ an outcome, recorded only on $R$. The observed-data map $O : \Omega \to \mathcal X \times (\mathcal Y \sqcup \{\ast\})$ pairs the covariate with the outcome of a respondent and with a missing marker $\ast$ for a nonrespondent:

$$O(\omega) = \begin{cases} (X(\omega), Y(\omega)) & \omega \in R, \\ (X(\omega), \ast) & \omega \notin R, \end{cases}$$

The second coordinate lies in the disjoint union $\mathcal Y \sqcup \{\ast\}$ with its sum measurable structure.
