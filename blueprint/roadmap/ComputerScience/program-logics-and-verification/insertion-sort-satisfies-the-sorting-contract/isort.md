# Insertion sort of a list

For a linearly ordered type $\alpha$, insertion sort under $\le$ is

$$\mathrm{isort}([]) = [], \qquad \mathrm{isort}(x :: xs) = \mathrm{insert}(x, \mathrm{isort}(xs)),$$

where $\mathrm{insert}$ is ordered insertion under $\le$.
