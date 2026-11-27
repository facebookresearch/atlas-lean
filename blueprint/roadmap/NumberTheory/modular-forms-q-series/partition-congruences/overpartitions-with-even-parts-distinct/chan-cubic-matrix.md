# Chan's matrix

Chan's matrix $(m_{i,j})_{i,j \ge 1}$ is the integer matrix with first
column $m_{1,1} = 3$, $m_{2,1} = 2$, $m_{3,1} = 1$ and $m_{i,1} = 0$ for $i \ge 4$, and with
$m_{i,j} = 9 m_{i-1,j-1} + 3 m_{i-2,j-1} + m_{i-3,j-1}$ for $i \ge 1$ and $j \ge 2$, where
entries with row index $\le 0$ are taken to be $0$.

The matrix extends to all natural indices by setting $m_{0,j} = m_{i,0} = 0$ for all $i$ and $j$;
the recursion then also holds for $i \ge 1$, $j \ge 2$ with the entries of row index $\le 0$ read
as row $0$.

## Sources

- Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Section 2 (from Hei-Chi Chan, "Ramanujan's cubic continued fraction and an analog of his 'most beautiful identity'," International Journal of Number Theory 6 (2010), 673–680, (11)-(19)).
