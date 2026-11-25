# In-sample LD correlation

Let $X$ be a real $n \times M$ matrix, let $S \subseteq \{1, \dots, n\}$ be a sample of individuals, and let $j, k$ be markers. The in-sample normalized cross product is

$$r^S_{jk} = \frac{1}{|S|} \sum_{i \in S} X_{ij} X_{ik},$$

with the convention $x/0 = 0$ when $S$ is empty. For a matrix standardized within $S$ it is the sample LD correlation of $j$ and $k$.
