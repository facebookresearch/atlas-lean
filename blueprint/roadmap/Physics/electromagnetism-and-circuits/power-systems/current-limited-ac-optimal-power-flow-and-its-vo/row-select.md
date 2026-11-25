# Matrix keeping one row of a square matrix

For a natural number $n$, a complex $n \times n$ matrix $Y$ and an index $k$, the row selection
$R_k$ is the $n \times n$ matrix that keeps row $k$ of $Y$ and has every other row zero:

$$(R_k)_{ab} = \begin{cases} Y_{kb} & \text{if } a = k, \\ 0 & \text{otherwise.} \end{cases}$$
