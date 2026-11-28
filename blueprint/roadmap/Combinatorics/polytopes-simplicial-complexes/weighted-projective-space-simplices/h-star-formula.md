# The $h^*$ formula of a weight vector

For a list $q = (q_1, \dots, q_n)$ of natural
numbers, put $|q| = q_1 + \dots + q_n$ and define the weight statistic
$w(q,b) = b - \sum_{i=1}^n \lfloor q_i b / (1 + |q|) \rfloor$. The $h^*$ formula of $q$ is the
integer polynomial $\sum_{b=0}^{|q|} z^{w(q,b)}$.

The polynomial is defined separately from the Ehrhart-series condition. For positive weights,
Theorem 2.2 of Braun, Davis, and Solus identifies it as the Ehrhart numerator.

## Sources

- Benjamin Braun, Robert Davis, and Liam Solus, *Detecting the integer decomposition property and Ehrhart unimodality in reflexive simplices*, Adv. in Appl. Math. 100 (2018), 122–142, Theorem 2.2; restated by Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60, Theorem 5.
