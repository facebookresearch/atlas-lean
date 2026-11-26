# Global traceback from a cell

The global traceback from cell `(i, j)` of the table `T` with
fuel `n`, where `acc` holds the columns already emitted. A cell of the top row steps left and one
of the left column steps up; an interior cell steps diagonally if `T[i-1][j-1] + σ` gives the
cell, else up if `T[i-1][j] + gap` does, else left. The table and the sequences are arrays, so a
step reads its cells and letters in constant time.
