# Solution of Henderson's mixed-model equations

Let $X$ be a real $n \times p$ matrix, $Z$ a real $n \times q$ matrix, $G$ a real $q \times q$ matrix, $R$ a real $n \times n$ matrix and $y \in \mathbb{R}^n$. A pair $(b, u) \in \mathbb{R}^p \times \mathbb{R}^q$ solves Henderson's mixed-model equations if

$$X^\top R^{-1} X b + X^\top R^{-1} Z u = X^\top R^{-1} y \quad\text{and}\quad Z^\top R^{-1} X b + (Z^\top R^{-1} Z + G^{-1}) u = Z^\top R^{-1} y,$$

with the convention that the inverse of a singular matrix is $0$.
