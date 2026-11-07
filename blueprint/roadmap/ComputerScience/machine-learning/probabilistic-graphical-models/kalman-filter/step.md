# Kalman filter step

Given real $n \times n$ matrices $F$ and $Q$, a real $p \times n$
matrix $H$, a real $p \times p$ matrix $R$ and an observation $y \in \mathbb{R}^p$, one filter
step sends a belief to the update, with $H$, $R$ and $y$, of its prediction with $F$ and $Q$.
