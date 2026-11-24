# Torch counts after a step in the star model

Given the number $\mathrm{tor}(v)$ of torches
at each vertex $v$ of the star graph and a step $S$, a finite list of movements, the number of
torches at $v$ after $S$ is $\max(\mathrm{tor}(v) - a, 0) + b$, where $a$ is the number of
movements of $S$ that start at $v$ and $b$ is the number of movements of $S$ that end at $v$.

## Sources

- Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6, Definition (the star model).
