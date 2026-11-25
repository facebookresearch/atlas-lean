# Method body lookup finds a locally declared method

Let the class table `ct` be well formed and `C` a class with declaration `cd`.
If `cd` declares method `m` as `md`, the method body of `m` in `C` is the
parameter names of `md` together with its body (rule MB-CLASS).
