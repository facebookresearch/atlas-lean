---
article_id: af_4dba6b115137c8c8a7b89c0c
declaration: structure
origin: cited
statement: formalized
lean: FrameSingularity.HasFrameSingularity
---

# Definition 34.1

Let $f \colon U \rightarrow \mathbb{R}^{3}$ be a surface patch, whose domain contains the origin. Let $(X_{1}, X_{2})$ be a moving frame defined on $U \setminus \{0\}$. We say that the frame has a singularity of multiplicity $m \in \mathbb{Z}$ at 0 if it can be written as $X_{1} = \cos(m\theta) \tilde{X}_{1} - \sin(m\theta) \tilde{X}_{2}$ and $X_{2} = \sin(m\theta) \tilde{X}_{1} + \cos(m\theta) \tilde{X}_{2}$ where $\theta$ is the angular coordinate, and $(\tilde{X}_{1}, \tilde{X}_{2})$ is a moving frame which extends smoothly over $x = 0$. Passing to the matrices whose column vectors are the $X_{k}$ and $\tilde{X}_{k}$, one can write the relation as $X = \tilde{X} \exp(m\theta J)$ where $J = \left(\begin{smallmatrix} 0 & -1 \\ 1 & 0 \end{smallmatrix}\right)$ as usual.

## Depends on

- [Definition 12.1](../../part-01/chapter-2/040-definition-12-1.md)
- [Definition 18.1](../../part-01/lecture-18/055-definition-18-1.md)

## Sources

- [MIT 18.950 Differential Geometry (Fall 2008), Lecture 34](../../../../../sources/v1/DifferentialGeometry.md)
