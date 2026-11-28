# History of play on a reward table

Let $x = (x_{t,i})$ be a real reward table with $n$ rounds and $k$ arms, and let $a = (a_1, \dots, a_n)$ be a sequence of
arms. The history of playing $a$ on $x$ is $(a_1, x_{1,a_1}, \dots, a_n, x_{n,a_n})$, the arm chosen and the reward
observed in each round: a policy that chooses the arms $a$ on $x$ observes exactly this history. In the formal
statement, arms and rounds are counted from $0$: the history is a map from $\{0, \dots, n-1\}$ to
$\{0, \dots, k-1\} \times \mathbb{R}$ whose value at $s$ is the pair $(a_{s+1} - 1, x_{s+1,a_{s+1}})$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 11.1 (in round $t$ the learner observes the reward $x_{t,A_t}$ of the arm it chose). <https://tor-lattimore.com/downloads/book/book.pdf>
