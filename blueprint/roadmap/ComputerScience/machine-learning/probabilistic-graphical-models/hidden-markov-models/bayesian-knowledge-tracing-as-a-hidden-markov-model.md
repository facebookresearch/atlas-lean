# Bayesian knowledge tracing as a two-state hidden Markov model

In the standard knowledge-tracing model, with parameters $p_0, s, g, \ell \in [0, 1]$, the pairs $(K_j, O_j)$ follow a hidden-Markov path law: the latent states $K_j \in \{0, 1\}$ (unlearned, learned) form a Markov chain with $P(K_1 = 1) = p_0$ and no forgetting, and given the latent path the responses are independent, each $O_j$ depending only on $K_j$; at each step $j$ the response $O_j$ is emitted from $K_j$ before the learning transition: $P(O_j = 1 \mid K_j = 1) = 1 - s$, $P(O_j = 1 \mid K_j = 0) = g$, and $P(K_{j+1} = 1 \mid K_j = 0) = \ell$. Let $p = P(K_j = 1 \mid O_1, \dots, O_{j-1})$. If the observed response has positive conditional probability, then after a correct response $P(K_j = 1 \mid O_1, \dots, O_j) = p(1-s)/(p(1-s) + (1-p)g)$, after an incorrect response it is $ps/(ps + (1-p)(1-g))$, and the next prediction is $\tilde p + (1 - \tilde p)\ell$, where $\tilde p$ is that filtered value. These are one step of the hidden-Markov forward recursion for this two-state model.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Positive-evidence filtering for a finite hidden Markov model as conditional probability under the path law.

## Background

- [One step of the tabulated forward algorithm](forward-step.md): the general forward step.

## Sources

- B. van de Sande, "Properties of the Bayesian knowledge tracing model", *Journal of Educational Data Mining* 5(2):1–10, 2013, equations (8)–(10)
