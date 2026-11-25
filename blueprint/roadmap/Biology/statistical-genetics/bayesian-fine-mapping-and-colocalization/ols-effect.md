# Marginal least-squares effect estimate

Let $I$ be a finite index set (the samples). For a genotype vector $x \in \mathbb{R}^I$ and a phenotype vector $y \in \mathbb{R}^I$, the marginal least-squares effect estimate is

$$\hat\beta(x, y) = \frac{x^\top y}{x^\top x},$$

with the convention that it is $0$ when $x = 0$.
