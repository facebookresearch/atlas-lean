# Counting placements by families of occupied rows and columns

Let $n, m, k$ be natural numbers, let $\mathcal{R}$ be a finite family of sets of rows and $\mathcal{C}$ a finite family of sets of columns of the $n \times m$ board. The number of $k$-element sets of cells of the board whose set of occupied rows belongs to $\mathcal{R}$ and whose set of occupied columns belongs to $\mathcal{C}$ is

$$\sum_{R \in \mathcal{R}} \sum_{C \in \mathcal{C}} E_{|R|,|C|}(k),$$

where $E_{a,b}(k)$ is the number of $k$-element sets of cells of the $a \times b$ board that contain a cell in every row and a cell in every column.
