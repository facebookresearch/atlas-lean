# Free model of exceptions

For an exception type $E$ and a return type $\alpha$, the free carrier for exceptions is the free monad on the raise signature. A computation either returns a value of $\alpha$, or raises some $e : E$, after which no continuation can run, since a raise passes no value on. Which pure computations exist depends on $\alpha$, even when $E$ is empty.
