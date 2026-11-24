# Structural shared-service template

Let $\Gamma$ be a service environment. A process is a service template for $\Gamma$ if it is built
by the following rules: $\mathbf{0}$ is a template; an input $\mathrm{c}_s(\cdot).q$ on the trigger
of a service $s$ declared in $\Gamma$ is a template for every continuation $q$; and if $p$, $q$ are
templates then so are $p \mid q$, $\nu\,p$ and $!p$. Outputs, choices and inputs on other names are
not templates.
