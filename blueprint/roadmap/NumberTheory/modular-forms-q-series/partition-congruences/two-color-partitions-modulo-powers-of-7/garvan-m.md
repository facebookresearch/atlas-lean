# Garvan's matrix

Garvan's matrix $(m_{i,j})_{i,j \ge 1}$ is the array of natural
numbers defined as follows. For $1 \le i \le 7$, $m_{i,j}$ is the entry in row $i$ and column
$j$ of the tabulated rows of Garvan's matrix (Tables 1 and 2 of the source), and $0$ beyond the
printed columns. For $i \ge 8$, $m_{i,1} = m_{i,2} = 0$ and, for $j \ge 3$,

$$m_{i,j} = 7m_{i-3,j-1} + 35m_{i-2,j-1} + 49m_{i-1,j-1} + m_{i-7,j-2} + 7m_{i-6,j-2} +
21m_{i-5,j-2} + 49m_{i-4,j-2} + 147m_{i-3,j-2} + 343m_{i-2,j-2} + 343m_{i-1,j-2}.$$

Entries with $i = 0$ or $j = 0$ are set to $0$.

Lemma 1 of the source identifies these numbers as the coefficients of Garvan's modular
expansion; that identity is a separate statement and is not part of this definition.

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Section 1.
