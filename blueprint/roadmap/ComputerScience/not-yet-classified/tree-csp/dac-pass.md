# Directional arc consistency pass

Given a parent map on the variables of a constraint network and current domains, the pass processes the listed variables in order. At each variable $x$ with parent $p$ it revises the domain of $p$ against $x$, removing values of $p$ with no support in the domain of $x$, and counts $|D_p| \cdot |D_x|$ constraint checks; a variable without a parent leaves the domains unchanged at no cost. The result is the final domains together with the total count.
