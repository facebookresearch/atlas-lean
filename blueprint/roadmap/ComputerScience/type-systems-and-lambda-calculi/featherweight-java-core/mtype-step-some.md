# Method type lookup finds a locally declared method

Let the class table `ct` be well formed and `C` a class with declaration `cd`.
If `cd` declares method `m` as `md`, the method type of `m` in `C` is the
parameter classes of `md` together with its return class (rule MT-CLASS).
