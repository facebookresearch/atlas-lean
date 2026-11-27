# Bradley–Terry and Plackett–Luce preference models

The Bradley–Terry model turns a reward into pairwise preference probabilities through the logistic function of the reward difference; the Plackett–Luce model extends it to rankings of several responses. Fitting the Bradley–Terry model by maximum likelihood is the usual way to learn a reward model from comparisons.

Let $X$ be a set of prompts, $Y$ a set of responses, $r : X \times Y \to \mathbb{R}$ a reward and $\sigma(t) = 1/(1 + e^{-t})$ the logistic function. The **Bradley–Terry model** with reward $r$ assigns to a prompt $x$ and responses $y_1, y_2$ the probability that $y_1$ is preferred to $y_2$,

$$p_r(y_1 \succ y_2 \mid x) = \frac{e^{r(x,y_1)}}{e^{r(x,y_1)} + e^{r(x,y_2)}} = \sigma\bigl(r(x,y_1) - r(x,y_2)\bigr).$$

A preference distribution $p^*$ follows the Bradley–Terry model if $p^* = p_{r^*}$ for some latent reward $r^*$; its probabilities then lie in $(0,1)$ and satisfy $p^*(y_1 \succ y_2 \mid x) + p^*(y_2 \succ y_1 \mid x) = 1$.

The **Plackett–Luce model** with reward $r$ assigns to a prompt $x$, responses $y_1, \dots, y_K$ and a ranking given by a permutation $\tau$ of $\{1, \dots, K\}$ (with $y_{\tau(1)}$ ranked first) the probability

$$p_r(\tau \mid y_1, \dots, y_K, x) = \prod_{k=1}^{K} \frac{e^{r(x, y_{\tau(k)})}}{\sum_{j=k}^{K} e^{r(x, y_{\tau(j)})}};$$

for $K = 2$ it is the Bradley–Terry model.

**Reward learning.** Given a finite dataset $\mathcal{D} = \{(x^{(i)}, y_w^{(i)}, y_l^{(i)})\}_{i=1}^{N}$ with $N \ge 1$ of comparisons in which $y_w^{(i)}$ was preferred to $y_l^{(i)}$, the Bradley–Terry negative log-likelihood of a reward $r$ is

$$\mathcal{L}_R(r, \mathcal{D}) = -\mathbb{E}_{(x, y_w, y_l) \sim \mathcal{D}} \log \sigma\bigl(r(x, y_w) - r(x, y_l)\bigr),$$

the expectation being the average over $\mathcal{D}$. For finite nonempty $X$ and $Y$, a prompt distribution $\rho$, a policy $\mu$ that generates the compared responses, and arbitrary preference probabilities $p^*(y \succ y' \mid x) \in [0,1]$, its population form is

$$\mathcal{L}_{\mathrm{BT}}(r) = -\mathbb{E}_{x \sim \rho,\ y, y' \sim \mu(\cdot \mid x)}\Bigl[p^*(y \succ y' \mid x) \log \sigma\bigl(r(x,y) - r(x,y')\bigr)\Bigr],$$

with $y$ and $y'$ drawn independently.

## Depends on

None.

## Proof depends on

None.

## Expansion

Both models see the reward only through differences between responses to the same prompt, so rewards that differ by a function of the prompt give the same preferences ([equivalent rewards induce the same preferences](equivalent-rewards-give-equal-preferences.md)); maximum-likelihood guarantees therefore need identifiability constraints, such as normalizing rewards to mean zero. When observed preferences are deterministic, $p^*(y \succ y') = 1$, no finite reward fits them: the fitted reward gap must diverge, and the population loss may have no minimizer. The models go back to Bradley and Terry (1952), Plackett (1975) and Luce (1959).

## Sources

- R. Rafailov, A. Sharma, E. Mitchell, C. D. Manning, S. Ermon and C. Finn, *Direct Preference Optimization: Your Language Model is Secretly a Reward Model*, Advances in Neural Information Processing Systems 36 (NeurIPS 2023), doi:10.52202/075280-2338, Section 3, equations (1) and (2), and Appendix A.3 of the supplementary material (Plackett–Luce model). [publisher page](https://proceedings.neurips.cc/paper_files/paper/2023/hash/a85b405ed65c6477a4fe8302b5e06ce7-Abstract-Conference.html)
- M. Gheshlaghi Azar, M. Rowland, B. Piot, D. Guo, D. Calandriello, M. Valko and R. Munos, *A General Theoretical Paradigm to Understand Learning from Human Preferences*, Proceedings of the 27th International Conference on Artificial Intelligence and Statistics (AISTATS 2024), PMLR 238, Section 3.1.1, equations (1) and (2), Section 4.2, and Appendix B (population Bradley–Terry loss). [publisher page](https://proceedings.mlr.press/v238/gheshlaghi-azar24a.html)
