# Adjacently valid chain

A chain of branch steps
$(a_1, b_1, c_1), \dots, (a_r, b_r, c_r)$ is adjacently valid when for every $j$ with
$1 \le j < r$ we have $a_{j+1} + b_{j+1} = a_j$, $1 \le b_{j+1} \le a_{j+1}$ and
$1 \le c_{j+1} \le c_j$. Only consecutive steps are related, and nothing is required of the first
step alone; in particular every chain with at most one step is adjacently valid.
